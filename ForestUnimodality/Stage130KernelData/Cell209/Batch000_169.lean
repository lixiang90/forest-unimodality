import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell209.Parameters
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch000_049
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch050_099
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch100_149
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch150_199
import ForestUnimodality.BinomialMassData.Q57_107.Batch000_049
import ForestUnimodality.BinomialMassData.Q57_107.Batch050_099
import ForestUnimodality.BinomialMassData.Q57_107.Batch100_149
import ForestUnimodality.BinomialMassData.Q57_107.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree000.table
  base := (729346108041657349885156239/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709235990724668974305444640000000000000)
      linear := (-55244032382105153280993370000000000000)
      constant := (729346108041657349885156239000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree000.table
  base := (729346108041657349885156239/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709235990724668974305444640000000000000)
      linear := (-55244032382105153280993370000000000000)
      constant := (729346108041657349885156239000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree001.table
  base := (3180637303012117104286944465732798922467/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-421093406718797969479820598966883650000000000000)
      constant := (211590802440598004348621536510889628622124725507456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree001.table
  base := (407038907574587619389326837001355302135449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-9283749541602234048491906811850000000000000)
      constant := (4662829693908816563215782125027506854148755601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24946444514091848623/50000000000000000000)
  directionHi := (49892889028183697247/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree002.table
  base := (120097065431092613179494587852371864174141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-813491423320205389082438708391552330000000000000)
      constant := (125212486868440963684288121700763962615198776158042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree002.table
  base := (240108757337660644464079125466004890682563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-17935010156461746197069720530570000000000000)
      constant := (2758896260401331435119037023128989993424663787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24946444514091848623/50000000000000000000)
  centralHi := (49892889028183697247/100000000000000000000)
  directionLo := (3527960016481658737/5000000000000000000)
  directionHi := (70559200329633174741/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree003.table
  base := (7566680730001124535559630960162791299837/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-133987715546845867631672979757357890000000000000)
      constant := (8843714586841478122020702401659679359458685026660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree003.table
  base := (37816457398844151142277547610739603673899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-26586270771321258345647534249290000000000000)
      constant := (1753592052702742169178990412790560889849878604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3527960016481658737/5000000000000000000)
  centralHi := (70559200329633174741/100000000000000000000)
  directionLo := (86417018733209950237/100000000000000000000)
  directionHi := (43208509366604975119/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree004.table
  base := (12766720598377198662264717104429767980719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-1598287456523020228287674927240889690000000000000)
      constant := (54784283670219714577048681361242872998031074565112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree004.table
  base := (1595065542239522223360970606841894634489/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-35237531386180770494225347968010000000000000)
      constant := (1206978602314243585136361506995182506896931904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86417018733209950237/100000000000000000000)
  centralHi := (43208509366604975119/50000000000000000000)
  directionLo := (99785778056367394493/100000000000000000000)
  directionHi := (49892889028183697247/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree005.table
  base := (9177216318247830399187200203785963183837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-1990685473124427647890293036665558370000000000000)
      constant := (40824018500657927993137748542282866609615578127976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree005.table
  base := (36691046992609963740604557435664141505681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-43888792001040282642803161686730000000000000)
      constant := (899443954150886483819626789863987512197083538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99785778056367394493/100000000000000000000)
  centralHi := (49892889028183697247/50000000000000000000)
  directionLo := (111563891460872167747/100000000000000000000)
  directionHi := (27890972865218041937/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree006.table
  base := (6943433268366093620688108140345420692551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-264787054413981674165879016232247450000000000000)
      constant := (3634038750432932789257737588642770366515613338872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree006.table
  base := (1110428143559154667494799535107082954209/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-52540052615899794791380975405450000000000000)
      constant := (720641269320549027297224692126789637136942050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111563891460872167747/100000000000000000000)
  centralHi := (27890972865218041937/25000000000000000000)
  directionLo := (3055302997808883331/2500000000000000000)
  directionHi := (122212119912355333241/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree007.table
  base := (43629015990489732762878794847869700539651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-2775481506327242487095529255514895730000000000000)
      constant := (27889208634128180421843446915630156562126446781331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree007.table
  base := (4360928510287745934261774360749478805827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-61191313230759306939958789124170000000000000)
      constant := (614552317576691272701057088640257828479133230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3055302997808883331/2500000000000000000)
  centralHi := (122212119912355333241/100000000000000000000)
  directionLo := (132004176559117144103/100000000000000000000)
  directionHi := (16500522069889643013/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree008.table
  base := (35137314247621252790847379425246207939279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-3167879522928649906698147364939564410000000000000)
      constant := (25061004003268780955395781056789510906359358339999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree008.table
  base := (17560880679149974419478430305929180871097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-69842573845618819088536602842890000000000000)
      constant := (552280207586488556737280262317246383586379106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132004176559117144103/100000000000000000000)
  centralHi := (16500522069889643013/12500000000000000000)
  directionLo := (141118400659266349481/100000000000000000000)
  directionHi := (70559200329633174741/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree009.table
  base := (28737901032004196424105016887498748224339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-395586393281117480700085052707137010000000000000)
      constant := (2614286309806684863201231040425165115757524800651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree009.table
  base := (7181296132794634074082803707139816965613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-78493834460478331237114416561610000000000000)
      constant := (518555964321969605324432646109005057757212948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141118400659266349481/100000000000000000000)
  centralHi := (70559200329633174741/50000000000000000000)
  directionLo := (7483933354227554587/5000000000000000000)
  directionHi := (149678667084551091741/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree010.table
  base := (23700889757162925976213229336925611304653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-3952675556131464745903383583788901770000000000000)
      constant := (22912802232323109464351025236212332063205901605693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree010.table
  base := (5922548434587738174932615273854816117977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-87145095075337843385692230280330000000000000)
      constant := (505029135031809600509660798253755158938874692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7483933354227554587/5000000000000000000)
  centralHi := (149678667084551091741/100000000000000000000)
  directionLo := (31555033675017069501/20000000000000000000)
  directionHi := (78887584187542673753/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree011.table
  base := (4902074667668087594475424075494963280569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-4345073572732872165506001693213570450000000000000)
      constant := (22996568207131632011508587208643650241980676673956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree011.table
  base := (19599126679462481322362248736012300892629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-95796355690197355534270043999050000000000000)
      constant := (506917904039247390487919095857094832919709421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31555033675017069501/20000000000000000000)
  centralHi := (78887584187542673753/50000000000000000000)
  directionLo := (33095198522664996839/20000000000000000000)
  directionHi := (41368998153331246049/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree012.table
  base := (16206933441246056591980924495545131034677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-526385732148253287234291089182026570000000000000)
      constant := (2627595340217180174082465071826884145493941560893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree012.table
  base := (1619897518928814784757483844613108294627/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-104447616305056867682847857717770000000000000)
      constant := (521325580860622244307861775625154768651845230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33095198522664996839/20000000000000000000)
  centralHi := (41368998153331246049/25000000000000000000)
  directionLo := (86417018733209950237/50000000000000000000)
  directionHi := (6913361498656796019/4000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree013.table
  base := (13333670960187191548145795839420542107779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-5129869605935687004711237912062907810000000000000)
      constant := (24783440812477943414039362493580025200640713588499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree013.table
  base := (1665840248359760950994181533253808560503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-113098876919916379831425671436490000000000000)
      constant := (546385780646339161392257044696812833673590776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86417018733209950237/50000000000000000000)
  centralHi := (6913361498656796019/4000000000000000000)
  directionLo := (89945684836075503427/50000000000000000000)
  directionHi := (35978273934430201371/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree014.table
  base := (2175381419731001254653863848994064644407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-5522267622537094424313856021487576490000000000000)
      constant := (26343845961659564414487687196397936753188532220835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree014.table
  base := (10870822597178130714007348026418070856229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-121750137534775891980003485155210000000000000)
      constant := (580821430701502950676325395975840493232965821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89945684836075503427/50000000000000000000)
  centralHi := (35978273934430201371/20000000000000000000)
  directionLo := (186682096779796064633/100000000000000000000)
  directionHi := (93341048389898032317/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree015.table
  base := (6840771541243437987448822898867144703/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-657185071015389093768497125656916130000000000000)
      constant := (3143087018500010227473579162984769034595440674560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree015.table
  base := (1750171360447113633274345628813727230617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-130401398149635404128581298873930000000000000)
      constant := (623711799950773046826339261931891815316670165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186682096779796064633/100000000000000000000)
  centralHi := (93341048389898032317/50000000000000000000)
  directionLo := (1932343283003302117/1000000000000000000)
  directionHi := (193234328300330211701/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree016.table
  base := (863884536786509087091634886994778766303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-6307063655739909263519092240336913850000000000000)
      constant := (30583860128930423285939303939494502925970726714744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree016.table
  base := (863301102092801192282702102115114976103/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-139052658764494916277159112592650000000000000)
      constant := (674365188068158267446037454607167610891225976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1932343283003302117/1000000000000000000)
  centralHi := (193234328300330211701/100000000000000000000)
  directionLo := (199571556112734788987/100000000000000000000)
  directionHi := (49892889028183697247/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree017.table
  base := (1058958374959626660412503911773179940829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-6699461672341316683121710349761582530000000000000)
      constant := (33207777207318874863057956893011281098852031727745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree017.table
  base := (2645355163586178961955957011162420459167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-147703919379354428425736926311370000000000000)
      constant := (732246144632096039261315343842347103674005966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199571556112734788987/100000000000000000000)
  centralHi := (49892889028183697247/25000000000000000000)
  directionLo := (5142841285760546373/2500000000000000000)
  directionHi := (205713651430421854921/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree018.table
  base := (967591092598693502745802161337172518363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-787984409882524900302703162131805690000000000000)
      constant := (4015592346165676228806862287395300739013448769868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree018.table
  base := (773360144144569956441762259028860811231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-156355179994213940574314740030090000000000000)
      constant := (796931507586609812289960936520087137138918595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5142841285760546373/2500000000000000000)
  centralHi := (205713651430421854921/100000000000000000000)
  directionLo := (211677600988899524221/100000000000000000000)
  directionHi := (105838800494449762111/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree019.table
  base := (521633949066589267387387498492134791399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-7484257705544131522326946568610919890000000000000)
      constant := (39366134250007996023124251802522403854776920568595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree019.table
  base := (2605063338919776471048186099788187058357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-165006440609073452722892553748810000000000000)
      constant := (868082195808829516688524133730404953631129293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211677600988899524221/100000000000000000000)
  centralHi := (105838800494449762111/50000000000000000000)
  directionLo := (217478061275141980681/100000000000000000000)
  directionHi := (108739030637570990341/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree020.table
  base := (1484251962664394885128031175293256795479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-7876655722145538941929564678035588570000000000000)
      constant := (42872743134239548241420184054480402483726739212199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree020.table
  base := (1481548448710190941080433922883193189651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-173657701223932964871470367467530000000000000)
      constant := (945424008805031961689001313399689678828314299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217478061275141980681/100000000000000000000)
  centralHi := (108739030637570990341/50000000000000000000)
  directionLo := (111563891460872167747/50000000000000000000)
  directionHi := (44625556584348867099/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree021.table
  base := (95824115963468892007226055802154974009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-918783748749660706836909198606695250000000000000)
      constant := (5183337094868681856081856046953140785006698978405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree021.table
  base := (2383856241001195182374330355424889801/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-182308961838792477020048181186250000000000000)
      constant := (1028733865078334411061286920677841912666329800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111563891460872167747/50000000000000000000)
  centralHi := (44625556584348867099/20000000000000000000)
  directionLo := (228637940611683511347/100000000000000000000)
  directionHi := (57159485152920877837/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree022.table
  base := (-105786726723162076216674061036638576771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-8661451755348353781134800896884925930000000000000)
      constant := (50689735787734229670535643605088138016522181839796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree022.table
  base := (-21259280548583598736112620059369873021/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-190960222453651989168625994904970000000000000)
      constant := (1117829526907344989617242644172905486475651420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228637940611683511347/100000000000000000000)
  centralHi := (57159485152920877837/25000000000000000000)
  directionLo := (234018393000914288101/100000000000000000000)
  directionHi := (117009196500457144051/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree023.table
  base := (-617797825995769825461549202582559639551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-9053849771949761200737419006309594610000000000000)
      constant := (54985072895533813982156429895108709041779098173538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree023.table
  base := (-1237362542971821911068546727038606250611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-199611483068511501317203808623690000000000000)
      constant := (1212561694590273959714202232591064997036754661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234018393000914288101/100000000000000000000)
  centralHi := (117009196500457144051/50000000000000000000)
  directionLo := (59819472497626673019/25000000000000000000)
  directionHi := (239277889990506692077/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree024.table
  base := (-984467988333380011142449426265498196087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-1049583087616796513371115235081584810000000000000)
      constant := (6614497990944343900309288193196475819044545364834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree024.table
  base := (-492616379432020362659227748423023631611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-208262743683371013465781622342410000000000000)
      constant := (1312807795477417129958909121527699209766742644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59819472497626673019/25000000000000000000)
  centralHi := (239277889990506692077/100000000000000000000)
  directionLo := (3055302997808883331/1250000000000000000)
  directionHi := (244424239824710666481/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree025.table
  base := (-526395121899940091812106446529497686747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-9838645805152576039942655225158931970000000000000)
      constant := (64321387860982706501917352722276242641163839311465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree025.table
  base := (-658324572572171002335160370671804157631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-216914004298230525614359436061130000000000000)
      constant := (1418467035377227275972571981855464056797130724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3055302997808883331/1250000000000000000)
  centralHi := (244424239824710666481/100000000000000000000)
  directionLo := (249464445140918486233/100000000000000000000)
  directionHi := (124732222570459243117/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree026.table
  base := (-3231967312235816185316240664077235042641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-10231043821753983459545273334583600650000000000000)
      constant := (69354023423264837369321195179118833764938963972479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree026.table
  base := (-1616555008302571826633678769554764303261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-225565264913090037762937249779850000000000000)
      constant := (1529456418703215513212553659692475006983929622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249464445140918486233/100000000000000000000)
  centralHi := (124732222570459243117/50000000000000000000)
  directionLo := (31800601843028503369/12500000000000000000)
  directionHi := (254404814744228026953/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree027.table
  base := (-235930638295218385012766219291645159611/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-1180382426483932319905321271556474370000000000000)
      constant := (8291698096541615761159790607206158171855447441616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree027.table
  base := (-471984571640503744551540974590043574049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-234216525527949549911515063498570000000000000)
      constant := (1645707527645945066626182324450798728965703992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31800601843028503369/12500000000000000000)
  centralHi := (254404814744228026953/100000000000000000000)
  directionLo := (259251056199629850711/100000000000000000000)
  directionHi := (32406382024953731339/12500000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree028.table
  base := (-4265678463069397274127155042666108387017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-11015839854956798298750509553432938010000000000000)
      constant := (80132603252757050562131770617031411526020335148423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree028.table
  base := (-2133264598677204861885744001678743375947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-242867786142809062060092877217290000000000000)
      constant := (1767163904467174630363059507753440134177565594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259251056199629850711/100000000000000000000)
  centralHi := (32406382024953731339/12500000000000000000)
  directionLo := (264008353118234288207/100000000000000000000)
  directionHi := (16500522069889643013/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree029.table
  base := (-2354203824147684715345183387354440076213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-11408237871558205718353127662857606690000000000000)
      constant := (85873867595084578747520592441813131803308131443894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree029.table
  base := (-1177285218851386121385399547666347223711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-251519046757668574208670690936010000000000000)
      constant := (1893778917548939269163962503998101962542931044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264008353118234288207/100000000000000000000)
  centralHi := (16500522069889643013/6250000000000000000)
  directionLo := (268681430120842072249/100000000000000000000)
  directionHi := (1074725720483368289/400000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree030.table
  base := (-638305886642103120817329808078997872901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-1311181765351068126439527308031363930000000000000)
      constant := (10205258418731624969813152786411281287126093355928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree030.table
  base := (-159596207041678452574321333049230160059/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-260170307372528086357248504654730000000000000)
      constant := (2025514017901512676349625070586319644719504288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268681430120842072249/100000000000000000000)
  centralHi := (1074725720483368289/400000000000000000)
  directionLo := (68318651949595541403/25000000000000000000)
  directionHi := (273274607798382165613/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree031.table
  base := (-5462584524308928465125110947149067596041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-12193033904761020557558363881706944050000000000000)
      constant := (98051529745258815387079555702473225550390986507079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree031.table
  base := (-1365782033704587412904171274585450763391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-268821567987387598505826318373450000000000000)
      constant := (2162337312186652921179497147362574696839745764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68318651949595541403/25000000000000000000)
  centralHi := (273274607798382165613/100000000000000000000)
  directionLo := (277791849489754194771/100000000000000000000)
  directionHi := (69447962372438548693/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree032.table
  base := (-2889564127033230883159700689837749007477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-12585431921362427977160981991131612730000000000000)
      constant := (104485280519209001001996065994459824382576310550326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree032.table
  base := (-1155919183998157956023307867009459621623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-277472828602247110654404132092170000000000000)
      constant := (2304222393101172431821821641797843483960191365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277791849489754194771/100000000000000000000)
  centralHi := (69447962372438548693/25000000000000000000)
  directionLo := (141118400659266349481/50000000000000000000)
  directionHi := (282236801318532698963/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree033.table
  base := (-6057991043788315057263113574800876353651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-1441981104218203932973733344506253490000000000000)
      constant := (12349731616155812835891879153717725252316957542741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree033.table
  base := (-3029196582449861909294050462940360932779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-286124089217106622802981945810890000000000000)
      constant := (2451147379498897722683916838006421615361226458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141118400659266349481/50000000000000000000)
  centralHi := (282236801318532698963/100000000000000000000)
  directionLo := (286612826639171112649/100000000000000000000)
  directionHi := (5732256532783422253/2000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree034.table
  base := (-3150379505033278948665738812941070227257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-13370227954565242816366218209980950090000000000000)
      constant := (118037617947803311451816008542778339772614597969966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree034.table
  base := (-6301104604617863206172513352082764454091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-294775349831966134951559759529610000000000000)
      constant := (2603094127747981320499055784271584429765112141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286612826639171112649/100000000000000000000)
  centralHi := (5732256532783422253/2000000000000000000)
  directionLo := (290923035818194031429/100000000000000000000)
  directionHi := (29092303581819403143/10000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree035.table
  base := (-6508748300369854193016396927360161050677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-13762625971166650235968836319405618770000000000000)
      constant := (125154697080352191737918051263159023229588221055963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree035.table
  base := (-6509045179393280468508725682876355077833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-303426610446825647100137573248330000000000000)
      constant := (2760047583097523042921198152699798610713889983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290923035818194031429/100000000000000000000)
  centralHi := (29092303581819403143/10000000000000000000)
  directionLo := (295170312100070220649/100000000000000000000)
  directionHi := (5903406242001404413/2000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree036.table
  base := (-13366103510232066391636546794722309207/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-1572780443085339739507939380981143050000000000000)
      constant := (14722028254366593269612635333877498767501368168500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree036.table
  base := (-1670826669216369074387193141304113708699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-312077871061685159248715386967050000000000000)
      constant := (2921995245670838246528185098618076808596420596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295170312100070220649/100000000000000000000)
  centralHi := (5903406242001404413/2000000000000000000)
  directionLo := (7483933354227554587/2500000000000000000)
  directionHi := (299357334169102183481/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree037.table
  base := (-6824577361504404797808168240648809162939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-14547422004369465075174072538254956130000000000000)
      constant := (140067817939143464896944393017071858642214718207541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree037.table
  base := (-53318720060717249531230747840075104391/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-320729131676544671397293200685770000000000000)
      constant := (3088926730415054928202492431163459456617912448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7483933354227554587/2500000000000000000)
  centralHi := (299357334169102183481/100000000000000000000)
  directionLo := (151743297954481474709/50000000000000000000)
  directionHi := (303486595908962949419/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree038.table
  base := (-6934079971592210762779336370953566833661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-14939820020970872494776690647679624810000000000000)
      constant := (147862995937321272866103068549891446371279286707859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree038.table
  base := (-6934267707625404214060970622461404175161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-329380392291404183545871014404490000000000000)
      constant := (3260833404148603276104480166221219383598581711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151743297954481474709/50000000000000000000)
  centralHi := (303486595908962949419/100000000000000000000)
  directionLo := (307560423773912790439/100000000000000000000)
  directionHi := (7689010594347819761/2500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree039.table
  base := (-3506093743604784429041444752519122278473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-1703579781952475546042145417456032610000000000000)
      constant := (17320384681442827327322458269924753304248394765086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree039.table
  base := (-1753087126725613120924445287671313666283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-338031652906263695694448828123210000000000000)
      constant := (3437708085938741421104185102969934519338903732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307560423773912790439/100000000000000000000)
  centralHi := (7689010594347819761/2500000000000000000)
  directionLo := (62316198423064118471/20000000000000000000)
  directionHi := (77895248028830148089/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree040.table
  base := (-1411884499015627921421105114274962490457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-15724616054173687333981926866528962170000000000000)
      constant := (164128945079081857174888515110736302486474774728915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree040.table
  base := (-7059560553013503038140091346105137187773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-346682913521123207843026641841930000000000000)
      constant := (3619544799551605972940188653299642284337186923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62316198423064118471/20000000000000000000)
  centralHi := (77895248028830148089/25000000000000000000)
  directionLo := (315550336750170695011/100000000000000000000)
  directionHi := (78887584187542673753/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree041.table
  base := (-707622015714750995899580568163426105883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-16117014070775094753584544975953630850000000000000)
      constant := (172599218739577849265984240274287746623291210866770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree041.table
  base := (-283053539558488098559149993362128920453/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-355334174135982719991604455560650000000000000)
      constant := (3806338568759448181842612191298914649743340075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315550336750170695011/100000000000000000000)
  centralHi := (78887584187542673753/25000000000000000000)
  directionLo := (31947036701191047941/10000000000000000000)
  directionHi := (319470367011910479411/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree042.table
  base := (-3531471507935763277992741591706829975027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-1834379120819611352576351453930922170000000000000)
      constant := (20143788311018030188954659905618231575955663871914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree042.table
  base := (-3531522204146638967208242341458896544991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-363985434750842232140182269279370000000000000)
      constant := (3998085247953274466405457683312774186912796082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31947036701191047941/10000000000000000000)
  centralHi := (319470367011910479411/100000000000000000000)
  directionLo := (323342876486097081009/100000000000000000000)
  directionHi := (32334287648609708101/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree043.table
  base := (-219371664238754291598918047107470305931/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-16901810103977909592789781194802968210000000000000)
      constant := (190213416294293850644219638058634686266995224383648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree043.table
  base := (-701998010742222743921906119623677298183/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-372636695365701744288760082998090000000000000)
      constant := (4194781381865923790143896882381015186131028330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323342876486097081009/100000000000000000000)
  centralHi := (32334287648609708101/10000000000000000000)
  directionLo := (81792388150534095777/25000000000000000000)
  directionHi := (327169552602136383109/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree044.table
  base := (-138946457296208165695357425646778528799/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-17294208120579317012392399304227636890000000000000)
      constant := (199357052334740659590270684563841111800414305844050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree044.table
  base := (-6947397239669434519654518477734372355261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-381287955980561256437337896716810000000000000)
      constant := (4396424089318531081893952008805099170904616811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81792388150534095777/25000000000000000000)
  centralHi := (327169552602136383109/100000000000000000000)
  directionLo := (33095198522664996839/10000000000000000000)
  directionHi := (330951985226649968391/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree045.table
  base := (-6845442063669104992229629111801535079073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-1965178459686747159110557490405811730000000000000)
      constant := (23191654858427356018597136726153953796368533537143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree045.table
  base := (-6845505736215460037075462659523574918993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-389939216595420768585915710435530000000000000)
      constant := (4603010966809010100353997074978464590752449143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33095198522664996839/10000000000000000000)
  centralHi := (330951985226649968391/100000000000000000000)
  directionLo := (167345837191308251621/50000000000000000000)
  directionHi := (334691674382616503243/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree046.table
  base := (-839303287364496824963035460907769344801/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-18079004153782131851597635523076974250000000000000)
      constant := (218316849335387202212623034167364704937967500492152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree046.table
  base := (-3357240397229122247510082973664437886153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-398590477210280280734493524154250000000000000)
      constant := (4814540008502351824699022402417771701282868606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167345837191308251621/50000000000000000000)
  centralHi := (334691674382616503243/100000000000000000000)
  directionLo := (338390037200592011229/100000000000000000000)
  directionHi := (33839003720059201123/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree047.table
  base := (-409651378263540991850283869058209704503/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-18471402170383539271200253632501642930000000000000)
      constant := (228132843076438798634995828326333317735392439143312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree047.table
  base := (-6554468681221022616932866285833639281627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-407241737825139792883071337872970000000000000)
      constant := (5031009539789697040580314910894340663864652477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338390037200592011229/100000000000000000000)
  centralHi := (33839003720059201123/10000000000000000000)
  directionLo := (68409682838673268739/20000000000000000000)
  directionHi := (21378025887085396481/6250000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree048.table
  base := (-6365551666877087383012719510544541659679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-2095977798553882965644763526880701290000000000000)
      constant := (26463645711139624141323937012193644889935747385289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree048.table
  base := (-6365591554771393566453417655829055558037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-415892998439999305031649151591690000000000000)
      constant := (5252418162081040005173361912182093142916034387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68409682838673268739/20000000000000000000)
  centralHi := (21378025887085396481/6250000000000000000)
  directionLo := (86417018733209950237/25000000000000000000)
  directionHi := (345668074932839800949/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree049.table
  base := (-6147917360984667952037525606109211885923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-19256198203586354110405489851350980290000000000000)
      constant := (248436701211732128128288442811415612632683607719437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree049.table
  base := (-245918058956562901689265431408740286237/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-424544259054858817180226965310410000000000000)
      constant := (5478764706905125534168821666012263311571814675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86417018733209950237/25000000000000000000)
  centralHi := (345668074932839800949/100000000000000000000)
  directionLo := (349250223197285880727/100000000000000000000)
  directionHi := (43656277899660735091/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree050.table
  base := (-590160456602128811608784794258546078941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-19648596220187761530008107960775648970000000000000)
      constant := (258924468135217945443952780938305734099418755521790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree050.table
  base := (-5901633733088131830763885913234074192513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-433195519669718329328804779029130000000000000)
      constant := (5710048197725920688958597286760883084569918663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349250223197285880727/100000000000000000000)
  centralHi := (43656277899660735091/12500000000000000000)
  directionLo := (176398000824082936851/50000000000000000000)
  directionHi := (352796001648165873703/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree051.table
  base := (-1406671176455376995606059856214977437531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-2226777137421018772178969563355590850000000000000)
      constant := (29959563896783829762846530301238254147228255663284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree051.table
  base := (-1125341927655131273136813209290549391263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-441846780284577841477382592747850000000000000)
      constant := (5946267818161236579137514276150652500097149565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176398000824082936851/50000000000000000000)
  centralHi := (352796001648165873703/100000000000000000000)
  directionLo := (356306496088004703433/100000000000000000000)
  directionHi := (178153248044002351717/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree052.table
  base := (-5323217510882535697404821205712350818323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-20433392253390576369213344179624986330000000000000)
      constant := (280571490993448584594433017947783512661678395155037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree052.table
  base := (-5323238818669519920713397201152128164383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-450498040899437353625960406466570000000000000)
      constant := (6187422885516443992870238374766209284645979033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356306496088004703433/100000000000000000000)
  centralHi := (178153248044002351717/50000000000000000000)
  directionLo := (89945684836075503427/25000000000000000000)
  directionHi := (359782739344302013709/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree053.table
  base := (-4991252946662518754267597156177402943703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-20825790269991983788815962289049655010000000000000)
      constant := (291730689948858309059131950640415132848293889751257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree053.table
  base := (-623908894085580056521723272761668441613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-459149301514296865774538220185290000000000000)
      constant := (6433512828733570534474840071599843264095782104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89945684836075503427/25000000000000000000)
  centralHi := (359782739344302013709/100000000000000000000)
  directionLo := (72645142963771120201/20000000000000000000)
  directionHi := (181612857409427800503/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree054.table
  base := (-2315416410501339646696706000304314851617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-2357576476288154578713175599830480410000000000000)
      constant := (33679294469005556882743045710595293713878004301294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree054.table
  base := (-4630848373402266147474910879335605562309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-467800562129156377923116033904010000000000000)
      constant := (6684537170010568993453665964488266651917124259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72645142963771120201/20000000000000000000)
  centralHi := (181612857409427800503/50000000000000000000)
  directionLo := (9165908993426649993/2500000000000000000)
  directionHi := (366636359737065999721/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree055.table
  base := (-4241992124664549382287667715237132008781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-21610586303194798628021198507898992370000000000000)
      constant := (314720353634783592702203798798320554062573995971139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree055.table
  base := (-4242005407398133831194809757321856239841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-476451822744015890071693847622730000000000000)
      constant := (6940495509473073758902122091052072067910060391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9165908993426649993/2500000000000000000)
  centralHi := (366636359737065999721/100000000000000000000)
  directionLo := (370015568127647736763/100000000000000000000)
  directionHi := (92503892031911934191/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree056.table
  base := (-764952029953385765252246280959427835757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-22002984319796206047623816617323661050000000000000)
      constant := (326550784974863127334705627043258370436651105482415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree056.table
  base := (-1912385745851845813993778335246987654163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-485103083358875402220271661341450000000000000)
      constant := (7201387512386311781241043959731754476694975626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370015568127647736763/100000000000000000000)
  centralHi := (92503892031911934191/25000000000000000000)
  directionLo := (186682096779796064633/50000000000000000000)
  directionHi := (373364193559592129267/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree057.table
  base := (-1689580711647573907634006011047956809339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-2488375815155290385247381636305369970000000000000)
      constant := (37622770166804938876660607533123485797932947868698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree057.table
  base := (-3379171106041976362800436448417799572563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-493754343973734914368849475060170000000000000)
      constant := (7467212898481934011861610106513614612693726213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186682096779796064633/50000000000000000000)
  centralHi := (373364193559592129267/100000000000000000000)
  directionLo := (188341525830061723789/50000000000000000000)
  directionHi := (376683051660123447579/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree058.table
  base := (-726304121639165195850781981544885593713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-22787780352999020886829052836172998410000000000000)
      constant := (350882782544162781988299258209983006838004643217788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree058.table
  base := (-2905224751185116011622362425760697349033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-502405604588594426517427288778890000000000000)
      constant := (7737971433046600357566723462629045776050921183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188341525830061723789/50000000000000000000)
  centralHi := (376683051660123447579/100000000000000000000)
  directionLo := (189986461217346934359/50000000000000000000)
  directionHi := (379972922434693868719/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree059.table
  base := (-2402942546241341624158072184718691951083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-23180178369600428306431670945597667090000000000000)
      constant := (363384329165952691367340484058519388691361689705477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree059.table
  base := (-120147479953412388495140698822328446827/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-511056865203453938666005102497610000000000000)
      constant := (8013662919478825432605682938725993232245553540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189986461217346934359/50000000000000000000)
  centralHi := (379972922434693868719/100000000000000000000)
  directionLo := (95808638101928385141/25000000000000000000)
  directionHi := (76646910481542708113/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree060.table
  base := (-1872354018422765714611692720503319916369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-2619175154022426191781587672780259530000000000000)
      constant := (41789951542053075499602624961704246383488833739079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree060.table
  base := (-1872360035975618528921115896701199536263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-519708125818313450814582916216330000000000000)
      constant := (8294287193070040894320231545212467966509324913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95808638101928385141/25000000000000000000)
  centralHi := (76646910481542708113/20000000000000000000)
  directionLo := (1932343283003302117/500000000000000000)
  directionHi := (386468656600660423401/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree061.table
  base := (-1313462983252647047162751502834532001337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-23964974402803243145636907164447004450000000000000)
      constant := (389058480406948395144873754645930487975511230516503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree061.table
  base := (-656734058266602484574219976778665516347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-528359386433172962963160729935050000000000000)
      constant := (8579844115806833935695654836527712117006686394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1932343283003302117/500000000000000000)
  centralHi := (386468656600660423401/100000000000000000000)
  directionLo := (77935184072483678867/20000000000000000000)
  directionHi := (12177372511325574823/3125000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree062.table
  base := (-726279565126440842314438796845410419957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-24357372419404650565239525273871673130000000000000)
      constant := (402231073492453336689655117251395817946747659456283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree062.table
  base := (-726283943270386697504551567312892213147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-537010647048032475111738543653770000000000000)
      constant := (8870333572025345689612328418374734697051679997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77935184072483678867/20000000000000000000)
  centralHi := (12177372511325574823/3125000000000000000)
  directionLo := (196428500532557962967/50000000000000000000)
  directionHi := (78571400213023185187/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree063.table
  base := (-22162450125703828701949085290753731913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-2749974492889561998315793709255149090000000000000)
      constant := (46180815414089854553406311289597850037240483827915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree063.table
  base := (-110815984045660787371266456496075355309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-545661907662891987260316357372490000000000000)
      constant := (9165755464777064223077103882592106433257067259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196428500532557962967/50000000000000000000)
  centralHi := (78571400213023185187/20000000000000000000)
  directionLo := (39601252967735143231/10000000000000000000)
  directionHi := (396012529677351432311/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree064.table
  base := (532931845486590923656895766795466855529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-25142168452607465404444761492721010490000000000000)
      constant := (429247272414399783599725444524625380461013501556249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree064.table
  base := (133232165604684058049398289750380457699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-554313168277751499408894171091210000000000000)
      constant := (9466109712788718650068844018584288423440783404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39601252967735143231/10000000000000000000)
  centralHi := (396012529677351432311/100000000000000000000)
  directionLo := (199571556112734788987/50000000000000000000)
  directionHi := (15965724489018783119/4000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree065.table
  base := (240989351545261430329392135434837694387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-25534566469208872824047379602145679170000000000000)
      constant := (443090871456572705562933034634680847093161074502735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree065.table
  base := (602472022176379678807322498466306876217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-562964428892611011557471984809930000000000000)
      constant := (9771396247918493725341476886601831494851616866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199571556112734788987/50000000000000000000)
  centralHi := (15965724489018783119/4000000000000000000)
  directionLo := (40224933115247370817/10000000000000000000)
  directionHi := (402249331152473708171/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree066.table
  base := (1905227483573854908348719789110679203947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-2880773831756697804849999745730038650000000000000)
      constant := (50795348139430196047330320435323927638344391572323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree066.table
  base := (1905225170982162295339192399509200642347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-571615689507470523706049798528650000000000000)
      constant := (10081615013027015103080255050609720838154230803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40224933115247370817/10000000000000000000)
  centralHi := (402249331152473708171/100000000000000000000)
  directionLo := (40533174658320449449/10000000000000000000)
  directionHi := (405331746583204494491/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree067.table
  base := (2633769827533355738408623973563725486527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-26319362502411687663252615820995016530000000000000)
      constant := (471449055630031874405965925608013180018888289407887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree067.table
  base := (1316883928428380405923369558888798891547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-580266950122330035854627612247370000000000000)
      constant := (10396765960195063623995556553053685717018643206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40533174658320449449/10000000000000000000)
  centralHi := (405331746583204494491/100000000000000000000)
  directionLo := (408390897503567972889/100000000000000000000)
  directionHi := (40839089750356797289/10000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree068.table
  base := (3390570270539082412405640430884705320417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-26711760519013095082855233930419685210000000000000)
      constant := (485963636754145847390100978823162320277363205096977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree068.table
  base := (169528429575139175524909473362857105443/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-588918210737189548003205425966090000000000000)
      constant := (10716849049231225079367260387442107020004338140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408390897503567972889/100000000000000000000)
  centralHi := (40839089750356797289/10000000000000000000)
  directionLo := (411427302860843709841/100000000000000000000)
  directionHi := (205713651430421854921/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree069.table
  base := (521953232572648717784713979319792175949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-3011573170623833611384205782204928210000000000000)
      constant := (55633541677094683464831509346449691568251764393128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree069.table
  base := (2087812215128610345869769499245974445927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-597569471352049060151783239684810000000000000)
      constant := (11041864246422052671145172756833164322862836446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411427302860843709841/100000000000000000000)
  centralHi := (205713651430421854921/50000000000000000000)
  directionLo := (414441462591434096809/100000000000000000000)
  directionHi := (41444146259143409681/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree070.table
  base := (1247233530270799243139381112782735142053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-27496556552215909922060470149269022570000000000000)
      constant := (515663769362743454415198715714173126886076317900372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree070.table
  base := (623616612853034758986375266276855312127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-606220731966908572300361053403530000000000000)
      constant := (11371811523485129850575443796106929731748336184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414441462591434096809/100000000000000000000)
  centralHi := (41444146259143409681/10000000000000000000)
  directionLo := (52179232322727323649/12500000000000000000)
  directionHi := (417433858581818589193/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree071.table
  base := (5830492974136024554355915917954362803181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030410000000000000000000000000000000000000000
      center := (15043986)
      previous := (7521993)
      next := (7521993)
      square := (73080385720260615781407321150240000000000000)
      linear := (-5532425028529521392910749505791250000000000000)
      constant := (105306351613071237204555296984953876747602573421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree071.table
  base := (5830491936662902433788232579360749577213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-614871992581768084448938867122250000000000000)
      constant := (11706690856691934099374758904668591221909511637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52179232322727323649/12500000000000000000)
  centralHi := (417433858581818589193/100000000000000000000)
  directionLo := (84080991113588658549/20000000000000000000)
  directionHi := (210202477783971646373/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree072.table
  base := (6700300676168520474975113056500907389077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-3142372509490969417918411818679817770000000000000)
      constant := (60695391282715055654624342334161369327924312110493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree072.table
  base := (1340059958557780422726576618485076803433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-623523253196627596597516680840970000000000000)
      constant := (12046502226132835407184290804812778221612522085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84080991113588658549/20000000000000000000)
  centralHi := (210202477783971646373/50000000000000000000)
  directionLo := (423355201977799048443/100000000000000000000)
  directionHi := (105838800494449762111/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree073.table
  base := (7598355764030955003346617176285732120137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-28673750602020132180868324477543028610000000000000)
      constant := (561891377791570239476121076369125161363764215586297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree073.table
  base := (7598355011971230704225567026188760386377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-632174513811487108746094494559690000000000000)
      constant := (12391245615101097523688013718861265117663630273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423355201977799048443/100000000000000000000)
  centralHi := (105838800494449762111/25000000000000000000)
  directionLo := (213142515360756733573/50000000000000000000)
  directionHi := (426285030721513467147/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree074.table
  base := (8524657009799044019980627014776411141803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-29066148618621539600470942586967697290000000000000)
      constant := (577747886585076003309329284833620389708211578054843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree074.table
  base := (8524656369632653416521148278416975971473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-640825774426346620894672308278410000000000000)
      constant := (12740921009576535687786149883579575957897394377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213142515360756733573/50000000000000000000)
  centralHi := (426285030721513467147/100000000000000000000)
  directionLo := (85838971986579693347/20000000000000000000)
  directionHi := (26824678745806154171/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree075.table
  base := (2369800845720646920366782402224313729913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-3273171848358105224452617855154707330000000000000)
      constant := (65980894154403739293872777046146859865660057665668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree075.table
  base := (236980070951029269884690581999371337399/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-649477035041206133043250121997130000000000000)
      constant := (13095528397792646237716892990104682097675246040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85838971986579693347/20000000000000000000)
  centralHi := (26824678745806154171/6250000000000000000)
  directionLo := (86417018733209950237/20000000000000000000)
  directionHi := (216042546833024875593/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree076.table
  base := (2092398803650770474793823995035524792411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-29850944651824354439676178805817034650000000000000)
      constant := (610131859755922110755509869429669644067948184754455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree076.table
  base := (5230996777304647697686489855771584762069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-658128295656065645191827935715850000000000000)
      constant := (13455067769873665029717262949392697747881855962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86417018733209950237/20000000000000000000)
  centralHi := (216042546833024875593/50000000000000000000)
  directionLo := (217478061275141980681/50000000000000000000)
  directionHi := (434956122550283961363/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree077.table
  base := (2868257047450981213341379473134334492001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-30243342668425761859278796915241703330000000000000)
      constant := (626659323306778853463643425052053018010059505926724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree077.table
  base := (717064237206943864857831997401503001873/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-666779556270925157340405749434570000000000000)
      constant := (13819539117530219244125929194060946925895103632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217478061275141980681/50000000000000000000)
  centralHi := (434956122550283961363/100000000000000000000)
  directionLo := (437808324406419085079/100000000000000000000)
  directionHi := (10945208110160477127/2500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree078.table
  base := (12512305287996708584196451725747224751667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-3403971187225241030986823891629596890000000000000)
      constant := (71490048636176971287539614885631535927432632669803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree078.table
  base := (1251230495238817385272270682008293640643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-675430816885784669488983563153290000000000000)
      constant := (14188942433804082773070845539876509538917217070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437808324406419085079/100000000000000000000)
  centralHi := (10945208110160477127/2500000000000000000)
  directionLo := (220321032413575387573/50000000000000000000)
  directionHi := (440642064827150775147/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree079.table
  base := (1697478100140655499203376483919640899037/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-31028138701628576698484033134091040690000000000000)
      constant := (660385202746567992351751662824578108465820736937576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree079.table
  base := (1697478064456297336729524824591515618261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-684082077500644181637561376872010000000000000)
      constant := (14563277712854088786737001858542516098507761512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220321032413575387573/50000000000000000000)
  centralHi := (440642064827150775147/100000000000000000000)
  directionLo := (88691539544809706599/20000000000000000000)
  directionHi := (110864424431012133249/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree080.table
  base := (14675586299587974739509403919466807938579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-31420536718229984118086651243515709370000000000000)
      constant := (677583618146556806387423455908547809837624357563299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree080.table
  base := (183444825709877041020549947908466498007/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-692733338115503693786139190590730000000000000)
      constant := (14942544949776544109918098059682722634854571440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88691539544809706599/20000000000000000000)
  centralHi := (110864424431012133249/25000000000000000000)
  directionLo := (446255565843488670989/100000000000000000000)
  directionHi := (44625556584348867099/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree081.table
  base := (1974948677837135511967237098761828436869/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-3534770526092376837521029928104486450000000000000)
      constant := (77222853748689691790249372106160697663696305163368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree081.table
  base := (15799589216223416637100343277929590801363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-701384598730363205934717004309450000000000000)
      constant := (15326744140454570256015039291440005885084804987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446255565843488670989/100000000000000000000)
  centralHi := (44625556584348867099/10000000000000000000)
  directionLo := (449036001253653275221/100000000000000000000)
  directionHi := (224518000626826637611/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree082.table
  base := (16951833867610118982350620885678044497371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-32205332751432798957291887462365046730000000000000)
      constant := (712651399364213892729632280548048006634473223868651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree082.table
  base := (16951833692048906015549634240805596881811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-710035859345222718083294818028170000000000000)
      constant := (15715875281431700011334263512801283278699854139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449036001253653275221/100000000000000000000)
  centralHi := (224518000626826637611/50000000000000000000)
  directionLo := (225899662902277013841/50000000000000000000)
  directionHi := (451799325804554027683/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree083.table
  base := (9066159690021165934510677649525881148699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-32597730768034206376894505571789715410000000000000)
      constant := (730520764892493760946744363934608592168875270270038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree083.table
  base := (4533079807696098646719097894820758769219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-718687119960082230231872631746890000000000000)
      constant := (16109938369805815246407778625967541468595153324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225899662902277013841/50000000000000000000)
  centralHi := (451799325804554027683/100000000000000000000)
  directionLo := (454545851562884920881/100000000000000000000)
  directionHi := (227272925781442460441/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree084.table
  base := (19341045746472612675456394971356680472913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-3665569864959512644055235964579376010000000000000)
      constant := (83179308912459736518645306167788529646696014303417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree084.table
  base := (19341045619592893910576080161638913977043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-727338380574941742380450445465610000000000000)
      constant := (16508933403140145280580248208215683926123165307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454545851562884920881/100000000000000000000)
  centralHi := (227272925781442460441/50000000000000000000)
  directionLo := (91455176244673404539/20000000000000000000)
  directionHi := (57159485152920877837/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree085.table
  base := (20578012787602315627644479035437870687579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-33382526801237021216099741790639052770000000000000)
      constant := (766930445230012457514695787951878462785318410632299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree085.table
  base := (10289006339879427193898825977822576059327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-735989641189801254529028259184330000000000000)
      constant := (16912860379388575786494426610624731346606469646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91455176244673404539/20000000000000000000)
  centralHi := (57159485152920877837/12500000000000000000)
  directionLo := (91997941699624023357/20000000000000000000)
  directionHi := (229994854249060058393/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree086.table
  base := (2184322035286518136671087070085349930257/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-33774924817838428635702359900063721450000000000000)
      constant := (785470759867909663419264892209935514567967657580170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree086.table
  base := (5460805065303230252183574381191651615189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-744640901804660766677606072903050000000000000)
      constant := (17321719296832962718643035671955792877369195444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91997941699624023357/20000000000000000000)
  centralHi := (229994854249060058393/50000000000000000000)
  directionLo := (2891797615534243771/625000000000000000)
  directionHi := (462687618485479003361/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree087.table
  base := (11568334157909571021193220166411261548277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-3796369203826648450589442001054265570000000000000)
      constant := (89359413784461275934785490945991773153656464046586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree087.table
  base := (5784167059484102004438707059504268138663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-753292162419520278826183886621770000000000000)
      constant := (17735510154030518143809853913572707463678210748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2891797615534243771/625000000000000000)
  centralHi := (462687618485479003361/100000000000000000000)
  directionLo := (465369888019565383547/100000000000000000000)
  directionHi := (116342472004891345887/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree088.table
  base := (12229178285139052201719748383445164932491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-34559720851041243474907596118913058810000000000000)
      constant := (823222337751581708951985836665206616473752373330742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree088.table
  base := (1528647281506493808198785774493497121187/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-761943423034379790974761700340490000000000000)
      constant := (18154232949769646891571244223142096776647519408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465369888019565383547/100000000000000000000)
  centralHi := (116342472004891345887/25000000000000000000)
  directionLo := (468036786001828576203/100000000000000000000)
  directionHi := (117009196500457144051/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree089.table
  base := (645207125676617308033505069101312895759/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-34952118867642650894510214228337727490000000000000)
      constant := (842433600895878964001154878307739510628761344915160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree089.table
  base := (25808284970845235748905508476586453352141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-770594683649239303123339514059210000000000000)
      constant := (18577887683032874454289992760398068304428662309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468036786001828576203/100000000000000000000)
  centralHi := (117009196500457144051/25000000000000000000)
  directionLo := (117672143428919735933/25000000000000000000)
  directionHi := (470688573715678943733/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree090.table
  base := (3398306701410514302229787831100795943367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-3927168542693784257123648037529155130000000000000)
      constant := (95763168161571185662934495866425536320908191000824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree090.table
  base := (13593226781763625411135776554443602630851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-779245944264098815271917327777930000000000000)
      constant := (19006474352965725764250613128686349613041226198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117672143428919735933/25000000000000000000)
  centralHi := (470688573715678943733/100000000000000000000)
  directionLo := (473325505125256042517/100000000000000000000)
  directionHi := (236662752562628021259/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree091.table
  base := (7148215565008851431948088091516592397869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-35736914900845465733715450447187064850000000000000)
      constant := (881527075393694201681316993730065149547978478999156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree091.table
  base := (14296431109735878495754019963473551635731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-787897204878958327420495141496650000000000000)
      constant := (19439992958850598233762890968830107385354968438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473325505125256042517/100000000000000000000)
  centralHi := (236662752562628021259/50000000000000000000)
  directionLo := (475947827159298456367/100000000000000000000)
  directionHi := (29746739197456153523/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree092.table
  base := (30027510920489777705411950316625345197413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-36129312917446873153318068556611733530000000000000)
      constant := (901409286687098715363918108908907404927407116615253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree092.table
  base := (30027510886039628600619239676122798982557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-796548465493817839569072955215370000000000000)
      constant := (19878443500084826513191331176592929925551295093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475947827159298456367/100000000000000000000)
  centralHi := (29746739197456153523/6250000000000000000)
  directionLo := (478555779981013384153/100000000000000000000)
  directionHi := (239277889990506692077/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree093.table
  base := (3936299943534639932191635950576499615351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-4057967881560920063657854074004044690000000000000)
      constant := (102390571923478562163004778012543666975459682340472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree093.table
  base := (31490399519022202250396314554855648587761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-805199726108677351717650768934090000000000000)
      constant := (20321825976162265615278391767984772320681275689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478555779981013384153/100000000000000000000)
  centralHi := (239277889990506692077/50000000000000000000)
  directionLo := (240574798622390383393/50000000000000000000)
  directionHi := (481149597244780766787/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree094.table
  base := (8245382026532794346478842431317031422881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-36914108950649687992523304775461070890000000000000)
      constant := (941844657246962035772092563063101238774916215723844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree094.table
  base := (16490764040645316805392833508528859180241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-813850986723536863866228582652810000000000000)
      constant := (20770140386657827401289289104700473817509158418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240574798622390383393/50000000000000000000)
  centralHi := (481149597244780766787/100000000000000000000)
  directionLo := (241864753170234271737/50000000000000000000)
  directionHi := (19349180253618741739/4000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree095.table
  base := (34500896562751895634478966235697253292849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-37306506967251095412125922884885739570000000000000)
      constant := (962397816477805466250461063522044306521730755651169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree095.table
  base := (34500896541661799980476233126557318637219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-822502247338396376014806396371530000000000000)
      constant := (21223386731214496299416712815734804741077520331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241864753170234271737/50000000000000000000)
  centralHi := (19349180253618741739/4000000000000000000)
  directionLo := (486295728626082063349/100000000000000000000)
  directionHi := (9725914572521641267/2000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree096.table
  base := (3604850489185007310266021904763114707901/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-4188767220428055870192060110478934250000000000000)
      constant := (109241624998909106617859763738748885343657138455090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree096.table
  base := (1441940194957839774600624516056553434123/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-831153507953255888163384210090250000000000000)
      constant := (21681565009532426354281177373694527006681855675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486295728626082063349/100000000000000000000)
  centralHi := (9725914572521641267/2000000000000000000)
  directionLo := (488848479649421332961/100000000000000000000)
  directionHi := (244424239824710666481/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree097.table
  base := (9406088267836272853181103592603615312573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-38091303000453910251331159103735076930000000000000)
      constant := (1004175082772622187142693513556281816438776034716852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree097.table
  base := (4703044132018405298724034382721527902991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-839804768568115400311962023808970000000000000)
      constant := (22144675221359785655267755356956580183690751672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488848479649421332961/100000000000000000000)
  centralHi := (244424239824710666481/50000000000000000000)
  directionLo := (245693984679687140013/50000000000000000000)
  directionHi := (491387969359374280027/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree098.table
  base := (19614220541345582817631030915339318765691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-38483701017055317670933777213159745610000000000000)
      constant := (1025399189815492917846550204141658450438940379749142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree098.table
  base := (39228441069791759585301101189165660079183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-848456029182974912460539837527690000000000000)
      constant := (22612717366485067843985082664747937642246566167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245693984679687140013/50000000000000000000)
  centralHi := (491387969359374280027/100000000000000000000)
  directionLo := (493914402307432223183/100000000000000000000)
  directionHi := (30869650144214513949/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree099.table
  base := (40860768910311511199895717525792299833649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-4319566559295191676726266146953823810000000000000)
      constant := (116316327345633678603545674185436739927899850348441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree099.table
  base := (2553798056210249914147792450605878654209/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-857107289797834424609117651246410000000000000)
      constant := (23085691444730635419107203106234517275392621456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493914402307432223183/100000000000000000000)
  centralHi := (30869650144214513949/6250000000000000000)
  directionLo := (99285595567994990517/20000000000000000000)
  directionHi := (248213988919987476293/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree100.table
  base := (21260668270561564063151855035559755661177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-39268497050258132510139013432009082970000000000000)
      constant := (1068518351651457057392474612093390170204046226389074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree100.table
  base := (10630334132958258905459662977590687603851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-865758550412693936757695464965130000000000000)
      constant := (23563597455947297333004404935684743129505960396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99285595567994990517/20000000000000000000)
  centralHi := (248213988919987476293/50000000000000000000)
  directionLo := (498928890281836972467/100000000000000000000)
  directionHi := (124732222570459243117/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree101.table
  base := (44210143964137679670581282330914411487747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-39660895066859539929741631541433751650000000000000)
      constant := (1090413406432047099478633810721634036976133159618707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree101.table
  base := (1381566998632962922021826177868899499681/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-874409811027553448906273278683850000000000000)
      constant := (24046435400009755076316323718367462971899128608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498928890281836972467/100000000000000000000)
  centralHi := (124732222570459243117/25000000000000000000)
  directionLo := (250708664555816642853/50000000000000000000)
  directionHi := (501417329111633285707/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree102.table
  base := (11481797792531568087111434682519321283551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-4450365898162327483260472183428713370000000000000)
      constant := (123614678938631052499096080497474233673345069545436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree102.table
  base := (11481797790859521112145940064995585706027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-883061071642412961054851092402570000000000000)
      constant := (24534205276812778052678960650992237842993212492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250708664555816642853/50000000000000000000)
  centralHi := (501417329111633285707/100000000000000000000)
  directionLo := (503893479129292386661/100000000000000000000)
  directionHi := (251946739564646193331/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree103.table
  base := (47672478151337899891042154400401362219429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-40445691100062354768946867760283089010000000000000)
      constant := (1134874463694328073718507039500720758850853457472149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree103.table
  base := (23836239072831921855431871382733305375753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-891712332257272473203428906121290000000000000)
      constant := (25026907086267991376793934824509957226493992194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503893479129292386661/100000000000000000000)
  centralHi := (251946739564646193331/50000000000000000000)
  directionLo := (506357520616215667973/100000000000000000000)
  directionHi := (253178760308107833987/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree104.table
  base := (12361501225315738810143783935435986449873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-40838089116663762188549485869707757690000000000000)
      constant := (1157440466168611620041094745931000441720311419522052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree104.table
  base := (49446004896449684478173792439515998452757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-900363592872131985352006719840010000000000000)
      constant := (25524540828301177973055035016311298666285614893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506357520616215667973/100000000000000000000)
  centralHi := (253178760308107833987/50000000000000000000)
  directionLo := (31800601843028503369/6250000000000000000)
  directionHi := (101761925897691210781/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree105.table
  base := (1601492856701081022384301024176345997671/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-4581165237029463289794678219903602930000000000000)
      constant := (131136679763076718839066797306118304166873108526048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree105.table
  base := (25623885705175938787660652364227039833801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-909014853486991497500584533558730000000000000)
      constant := (26027106502850012586135481096861220758114375298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31800601843028503369/6250000000000000000)
  centralHi := (101761925897691210781/20000000000000000000)
  directionLo := (511249977443284178709/100000000000000000000)
  directionHi := (51124997744328417871/10000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree106.table
  base := (53077777686261879348036677786683452033011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-41622885149866577027754722088557095050000000000000)
      constant := (1203243418789179955401837001840788762159985705199491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree106.table
  base := (13269444420699783392968525923689427976761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-917666114101851009649162347277450000000000000)
      constant := (26534604109862158523346255083851021043623746756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511249977443284178709/100000000000000000000)
  centralHi := (51124997744328417871/10000000000000000000)
  directionLo := (513678732099487680057/100000000000000000000)
  directionHi := (256839366049743840029/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree107.table
  base := (27468011856444822814632214078791795263949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6623874)
      previous := (3311937)
      next := (3311937)
      square := (32177327663187506695263717872160000000000000)
      linear := (-3669777549695867276387225102452770000000000000)
      constant := (107125545369121983415566908854637366168660204362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree107.table
  base := (54936023709952973348570578132425608908583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709235990724668974305444640000000000000)
      linear := (-80908146974994368224101682330000000000000)
      constant := (2362392667420182464603976835582425608908583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513678732099487680057/100000000000000000000)
  centralHi := (256839366049743840029/50000000000000000000)
  directionLo := (129024014282932008729/25000000000000000000)
  directionHi := (516096057131728034917/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree108.table
  base := (28411254745540380702863163181637631052429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-4711964575896599096328884256378492490000000000000)
      constant := (138882329810189100693020762561769398711701975498922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree108.table
  base := (14205627372147611580335577984187697731339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-934968635331570033946317974714890000000000000)
      constant := (27564395121107644566612508921074939805304400844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129024014282932008729/25000000000000000000)
  centralHi := (516096057131728034917/100000000000000000000)
  directionLo := (259251056199629850711/50000000000000000000)
  directionHi := (518502112399259701423/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree109.table
  base := (14684308754529311827504390717932707975723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-42800079199670799286562576416831101090000000000000)
      constant := (1273625216869641110583145310565246037921933814537452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree109.table
  base := (58737235016005618227556532221248831310891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-943619895946429546094895788433610000000000000)
      constant := (28086688525273104870058106858548907869678391059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259251056199629850711/50000000000000000000)
  centralHi := (518502112399259701423/100000000000000000000)
  directionLo := (260448527034649014429/50000000000000000000)
  directionHi := (520897054069298028859/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree110.table
  base := (60680200291717207073039274557838434640439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-43192477216272206706165194526255769770000000000000)
      constant := (1297533114663709916511567769374168034542322579469959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree110.table
  base := (30340100144963411801659668258540766395731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-952271156561289058243473602152330000000000000)
      constant := (28613913861764041649691603313639366468929448438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260448527034649014429/50000000000000000000)
  centralHi := (520897054069298028859/100000000000000000000)
  directionLo := (523281034735305352937/100000000000000000000)
  directionHi := (261640517367652676469/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree111.table
  base := (62651405309965048809391306654832805544271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-4842763914763734902863090292853382050000000000000)
      constant := (146851629074768145415610516503871007487049524100839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree111.table
  base := (62651405308447159399365561163066867270019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-960922417176148570392051415871050000000000000)
      constant := (29146071130558622772501961427589442563374447531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523281034735305352937/100000000000000000000)
  centralHi := (261640517367652676469/50000000000000000000)
  directionLo := (65706775441306101047/12500000000000000000)
  directionHi := (525654203530448808377/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree112.table
  base := (64650850071252868772628799581899597888961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-43977273249475021545370430745105107130000000000000)
      constant := (1346019857896416094339831389751106946605491285651441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree112.table
  base := (6465085006996610034708890497357829995397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-969573677791008082540629229589770000000000000)
      constant := (29683160331638523824688907658124897956173002530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65706775441306101047/12500000000000000000)
  centralHi := (525654203530448808377/100000000000000000000)
  directionLo := (264008353118234288207/50000000000000000000)
  directionHi := (105603341247293715283/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree113.table
  base := (66678534574231211518995551561909760279981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-44369671266076428964973048854529775810000000000000)
      constant := (1370598703333517326098903995692105895946767001516061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree113.table
  base := (16669633643285114018921000296914960044633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-978224938405867594689207043308490000000000000)
      constant := (30225181464988366619697091361199547510204012868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264008353118234288207/50000000000000000000)
  centralHi := (105603341247293715283/20000000000000000000)
  directionLo := (265184342694090730321/50000000000000000000)
  directionHi := (530368685388181460643/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree114.table
  base := (17183614704441926580560022325262682275197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-4973563253630870709397296329328271610000000000000)
      constant := (155044577553736535228066880584338981801571080854292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree114.table
  base := (68734458816843174987143270440742853861439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-986876199020727106837784857027210000000000000)
      constant := (30772134530595247543780923760668444933859615111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265184342694090730321/50000000000000000000)
  centralHi := (530368685388181460643/100000000000000000000)
  directionLo := (5327102803738317757/1000000000000000000)
  directionHi := (532710280373831775701/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree115.table
  base := (7081862280091231979211812052119146074167/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-45154467299279243804178285073379113170000000000000)
      constant := (1420427341846257091660091237201841396149219671507270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree115.table
  base := (70818622800128739239991844553387251843633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-995527459635586618986362670745930000000000000)
      constant := (31324019528448341363173359090745180646357754217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5327102803738317757/1000000000000000000)
  centralHi := (532710280373831775701/100000000000000000000)
  directionLo := (66880203441436184019/12500000000000000000)
  directionHi := (535041627531489472153/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree116.table
  base := (72931026522868166306139173738390055321223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-45546865315880651223780903182803781850000000000000)
      constant := (1445677134920988223876688219492034038074075215419863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree116.table
  base := (36465513261102048098359284042260068989969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1004178720250446131134940484464650000000000000)
      constant := (31880836458538568418227532132784911059732310162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66880203441436184019/12500000000000000000)
  centralHi := (535041627531489472153/100000000000000000000)
  directionLo := (537362860241684144499/100000000000000000000)
  directionHi := (1074725720483368289/200000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree117.table
  base := (75071669982966987230914031647584008426291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-5104362592498006515931502365803161170000000000000)
      constant := (163461175245275011148180668337335607292924405127019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree117.table
  base := (75071669982404240500191492426471343805987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1012829980865305643283518298183370000000000000)
      constant := (32442585320858315062609639207178420415234745163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537362860241684144499/100000000000000000000)
  centralHi := (1074725720483368289/200000000000000000)
  directionLo := (269837054508226510281/50000000000000000000)
  directionHi := (539674109016453020563/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree118.table
  base := (77240553180648552160253783802230408603531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-46331661349083466062986139401653119210000000000000)
      constant := (1496847668705426720729731417654815326786931762803611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree118.table
  base := (77240553180171702720929190534952899006057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1021481241480165155432096111902090000000000000)
      constant := (33009266115401198828821547455695655740720346593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269837054508226510281/50000000000000000000)
  centralHi := (539674109016453020563/100000000000000000000)
  directionLo := (54197550158497115651/10000000000000000000)
  directionHi := (541975501584971156511/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree119.table
  base := (7943767611544335487621582473629134842281/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-46724059365684873482588757511077787890000000000000)
      constant := (1522768409414599209599990983314885694935570051423610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree119.table
  base := (620606844648744684313279304021788970471/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1030132502095024667580673925620810000000000000)
      constant := (33580878842161871164621298323628349126134077312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54197550158497115651/10000000000000000000)
  centralHi := (541975501584971156511/100000000000000000000)
  directionLo := (544267162975922814159/100000000000000000000)
  directionHi := (6803339537199035177/1250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree120.table
  base := (8166303878695807709422394511474331964373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-5235161931365142322465708402278050730000000000000)
      constant := (172101422148309807305923980486794565229935967505570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree120.table
  base := (510393992416348505374063469654586627689/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1038783762709884179729251739339530000000000000)
      constant := (34157423501135851729932528603071657968065817760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544267162975922814159/100000000000000000000)
  centralHi := (6803339537199035177/1250000000000000000)
  directionLo := (68318651949595541403/12500000000000000000)
  directionHi := (21861968623870573249/4000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree121.table
  base := (16783328238972675469413261688710107296899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-47508855398887688321793993729927125250000000000000)
      constant := (1575280838465822819456452024664090336577270099296095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree121.table
  base := (83916641194573371777072573088353797078909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1047435023324743691877829553058250000000000000)
      constant := (34738900092319389205555600746793552622756429141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68318651949595541403/12500000000000000000)
  centralHi := (21861968623870573249/4000000000000000000)
  directionLo := (274410889655010334857/50000000000000000000)
  directionHi := (109764355862004133943/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree122.table
  base := (43099241669441816583464770735239919328677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-47901253415489095741396611839351793930000000000000)
      constant := (1601872526807559704218866850927762040473220856524074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree122.table
  base := (86198483338637960823399447578951967098739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1056086283939603204026407366776970000000000000)
      constant := (35325308615709344372773826592792521071313462811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274410889655010334857/50000000000000000000)
  centralHi := (109764355862004133943/20000000000000000000)
  directionLo := (551084971506750204911/100000000000000000000)
  directionHi := (34442810719171887807/6250000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree123.table
  base := (17701713043757664839887439309104899456987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-5365961270232278128999914438752940290000000000000)
      constant := (180965318262208797880713615335045555992072128128415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree123.table
  base := (4425428260929011074822113181198275694021/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1064737544554462716174985180495690000000000000)
      constant := (35916649071303091901441360032918711168416928580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551084971506750204911/100000000000000000000)
  centralHi := (34442810719171887807/6250000000000000000)
  directionLo := (553338907177305162221/100000000000000000000)
  directionHi := (276669453588652581111/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree124.table
  base := (18169377366876958768532468196957092237013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-48686049448691910580601848058201131290000000000000)
      constant := (1655726851122681178021837635297728068951796194914265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree124.table
  base := (45423443417104263398653072315136382489223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1073388805169322228323562994214410000000000000)
      constant := (36512921459098437854047853625057472886238228254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553338907177305162221/100000000000000000000)
  centralHi := (276669453588652581111/50000000000000000000)
  directionLo := (277791849489754194771/50000000000000000000)
  directionHi := (555583698979508389543/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree125.table
  base := (93213448185512168970465225305907229309087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-49078447465293318000204466167625799970000000000000)
      constant := (1682989487095882133228519899939676402504362910811247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree125.table
  base := (93213448185362876845737740276732748501923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1082040065784181740472140807933130000000000000)
      constant := (37114125779093550391964286761382063237598516427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277791849489754194771/50000000000000000000)
  centralHi := (555583698979508389543/100000000000000000000)
  directionLo := (34863716081522552421/6250000000000000000)
  directionHi := (557819457304360838737/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree126.table
  base := (19121649854407250510498473980163767430959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-5496760609099413935534120475227829850000000000000)
      constant := (190052863586601371180644630745688299829956234941155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree126.table
  base := (95608249271909815182134848968365465803879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1090691326399041252620718621651850000000000000)
      constant := (37720262031286901572184673835831556217988610671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34863716081522552421/6250000000000000000)
  centralHi := (557819457304360838737/100000000000000000000)
  directionLo := (5600462903393881939/1000000000000000000)
  directionHi := (560046290339388193901/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree127.table
  base := (49015645046922616798565102396628246284407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-49863243498496132839409702386475137330000000000000)
      constant := (1738185706673213722265976835284241077717447926568334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree127.table
  base := (49015645046869079408015086547467823664811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1099342587013900764769296435370570000000000000)
      constant := (38331330215677218460651154758066368226276842278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5600462903393881939/1000000000000000000)
  centralHi := (560046290339388193901/100000000000000000000)
  directionLo := (140566076032432375207/25000000000000000000)
  directionHi := (562264304129729500829/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree128.table
  base := (100482570650846083720975666113391899701251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-50255641515097540259012320495899806010000000000000)
      constant := (1766119290277237956445530376498488003009804802230931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree128.table
  base := (2512064266268885296575020874625588470957/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1107993847628760276917874249089290000000000000)
      constant := (38947330332263442071982972001626414496159467720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140566076032432375207/25000000000000000000)
  centralHi := (562264304129729500829/100000000000000000000)
  directionLo := (141118400659266349481/25000000000000000000)
  directionHi := (22578944105482615917/4000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree129.table
  base := (102962090942961530546846995266236347387193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-5627559947966549742068326511702719410000000000000)
      constant := (199364058121271656177581407534213497767520538163937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree129.table
  base := (102962090942884753429657832096728795668621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1116645108243619789066452062808010000000000000)
      constant := (39568262381044692883771714876409477981610041829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141118400659266349481/25000000000000000000)
  centralHi := (22578944105482615917/4000000000000000000)
  directionLo := (70834285974559825237/12500000000000000000)
  directionHi := (566674287796478601897/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree130.table
  base := (3295932842816484865267839775484445305937/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-51040437548300355098217556714749143370000000000000)
      constant := (1822657405115801295896988327087039547875693706115104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree130.table
  base := (10546985097006250789388988401913618300119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1125296368858479301215029876526730000000000000)
      constant := (40194126362020241873819831332990990159180624310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70834285974559825237/12500000000000000000)
  centralHi := (566674287796478601897/100000000000000000000)
  directionLo := (568866459571334641779/100000000000000000000)
  directionHi := (28443322978566732089/5000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree131.table
  base := (2700146268307276495735529572361307816443/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-51432835564901762517820174824173812050000000000000)
      constant := (1851261936350279608312210710006813815649761761787320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree131.table
  base := (108005850732236020417753678820257455464283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1133947629473338813363607690245450000000000000)
      constant := (40824922275189486196887708393061617607610576067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (568866459571334641779/100000000000000000000)
  centralHi := (28443322978566732089/5000000000000000000)
  directionLo := (285525108003133221663/50000000000000000000)
  directionHi := (571050216006266443327/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree132.table
  base := (110570090229408469791255346516074969844453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-5758359286833685548602532548177608970000000000000)
      constant := (208898901866095238590035037843500395809265426823277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree132.table
  base := (4422803609174474914835740072111606539891/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1142598890088198325512185503964170000000000000)
      constant := (41460650120551928758800903479051944581880301475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285525108003133221663/50000000000000000000)
  centralHi := (571050216006266443327/100000000000000000000)
  directionLo := (573225653278342225299/100000000000000000000)
  directionHi := (5732256532783422253/1000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree133.table
  base := (113162569461443832900334386677854754884997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-52217631598104577357025411043023149410000000000000)
      constant := (1909141946449515258782638124939425842832997183395957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree133.table
  base := (56581284730702192854536595991592514203041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1151250150703057837660763317682890000000000000)
      constant := (42101309898107161064457456783861315390221232818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573225653278342225299/100000000000000000000)
  centralHi := (5732256532783422253/1000000000000000000)
  directionLo := (71924108218311532937/12500000000000000000)
  directionHi := (575392865746492263497/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree134.table
  base := (115783288428367752700399988907554264733063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-52610029614705984776628029152447818090000000000000)
      constant := (1938417425314238673337282276310668699677984464242903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree134.table
  base := (115783288428334360061080227859889925964493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1159901411317917349809341131401610000000000000)
      constant := (42746901607854848815980856148818459762367480357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71924108218311532937/12500000000000000000)
  centralHi := (575392865746492263497/100000000000000000000)
  directionLo := (577551945999266392483/100000000000000000000)
  directionHi := (144387986499816598121/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree135.table
  base := (118432247130156287409995086032290415792383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-5889158625700821355136738584652498530000000000000)
      constant := (218657394821001661655815886509825100095071651546647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree135.table
  base := (118432247130128021593150057663857299635473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1168552671932776861957918945120330000000000000)
      constant := (43397425249794719821023831220719552223526530377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577551945999266392483/100000000000000000000)
  centralHi := (144387986499816598121/25000000000000000000)
  directionLo := (5797029849009906351/1000000000000000000)
  directionHi := (579702984900990635101/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree136.table
  base := (60554722783395029346425081120878197987039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-53394825647908799615833265371297155450000000000000)
      constant := (1997639330673834037794793446445325322450525019809118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree136.table
  base := (121109445566766133865950422826698738323489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1177203932547636374106496758839050000000000000)
      constant := (44052880823926553841592466971215113855065625561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5797029849009906351/1000000000000000000)
  centralHi := (579702984900990635101/100000000000000000000)
  directionLo := (581846071636388062859/100000000000000000000)
  directionHi := (29092303581819403143/5000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree137.table
  base := (123814883738253503495243979042221078287919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-53787223664510207035435883480721824130000000000000)
      constant := (2027585757168687838102603871107643284670319792323839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree137.table
  base := (61907441869116627031102024876753524821869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1185855193162495886255074572557770000000000000)
      constant := (44713268330250174072871755894917052211371156362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (581846071636388062859/100000000000000000000)
  centralHi := (29092303581819403143/5000000000000000000)
  directionLo := (291990646876862942169/50000000000000000000)
  directionHi := (583981293753725884339/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree138.table
  base := (126548561644534246060369300274122588407899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-6019957964567957161670944621127388090000000000000)
      constant := (228639536985952214165595970702058544226012141716691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree138.table
  base := (126548561644517108300415374320842220073533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1194506453777355398403652386276490000000000000)
      constant := (45378587768765439991192455278176102577621879317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291990646876862942169/50000000000000000000)
  centralHi := (583981293753725884339/100000000000000000000)
  directionLo := (586108737206547822447/100000000000000000000)
  directionHi := (36631796075409238903/6250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree139.table
  base := (129310479285622570889439462277436738433091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-54572019697713021874641119699571161490000000000000)
      constant := (2088149557788475259439637529485995506168230897973971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree139.table
  base := (129310479285608067393954906643244717799151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1203157714392214910552230199995210000000000000)
      constant := (46048839139472241351996844091293638774082479799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586108737206547822447/100000000000000000000)
  centralHi := (36631796075409238903/6250000000000000000)
  directionLo := (588228486394048064457/100000000000000000000)
  directionHi := (294114243197024032229/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree140.table
  base := (66050318330755490246954805560697339256003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-54964417714314429294243737808995830170000000000000)
      constant := (2118766931913399939532342095978598249309588831250086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree140.table
  base := (66050318330749353487935333047144829540623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1211808975007074422700808013713930000000000000)
      constant := (46724022442370493153707689108077722306821185454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588228486394048064457/100000000000000000000)
  centralHi := (294114243197024032229/50000000000000000000)
  directionLo := (295170312100070220649/50000000000000000000)
  directionHi := (590340624200140441299/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree141.table
  base := (134919033772193824366299156286114508467483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-6150757303435092968205150657602277650000000000000)
      constant := (238845328360926781414131033838766805321276277062547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree141.table
  base := (67459516886091719240711376527356353417623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1220460235621933934849385827432650000000000000)
      constant := (47404137677460131412847283217787395780556731454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295170312100070220649/50000000000000000000)
  centralHi := (590340624200140441299/100000000000000000000)
  directionLo := (296222616015637002883/50000000000000000000)
  directionHi := (592445232031274005767/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree142.table
  base := (4305177206802093367727277706208922641381/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030410000000000000000000000000000000000000000
      center := (15043986)
      previous := (7521993)
      next := (7521993)
      square := (73080385720260615781407321150240000000000000)
      linear := (-11059157656718358288722272173744330000000000000)
      constant := (432587309619777108055228896708052342632497267872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree142.table
  base := (68882835308829099820376252890392835623039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1229111496236793446997963641151370000000000000)
      constant := (48089184844741109620488014602118715150096347022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296222616015637002883/50000000000000000000)
  centralHi := (592445232031274005767/100000000000000000000)
  directionLo := (594542389853043824461/100000000000000000000)
  directionHi := (297271194926521912231/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree143.table
  base := (140640547197927630749884800653250266060389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-56141611764118651553051592137269836210000000000000)
      constant := (2211960949548264571317294568813299990964162985005909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree143.table
  base := (140640547197920194949059526206490644352069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1237762756851652959146541454870090000000000000)
      constant := (48779163944213395770895423503613841387186837981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594542389853043824461/100000000000000000000)
  centralHi := (297271194926521912231/50000000000000000000)
  directionLo := (298316088112821783797/50000000000000000000)
  directionHi := (119326435245128713519/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree144.table
  base := (143543663512973969373672554492809676050307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-6281556642302228774739356694077167210000000000000)
      constant := (249274768945916068325356791973203260582724922773563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree144.table
  base := (143543663512967678106408709136573740394563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1246414017466512471295119268588810000000000000)
      constant := (49474074975876969870681552902892312753777351787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298316088112821783797/50000000000000000000)
  centralHi := (119326435245128713519/20000000000000000000)
  directionLo := (598714668338204366961/100000000000000000000)
  directionHi := (299357334169102183481/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree145.table
  base := (36618754890701273087051333401614196421399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-56926407797321466392256828356119173570000000000000)
      constant := (2275208540688236059187860768807909344222704496574876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree145.table
  base := (73237509781399884850115593112469617736419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1255065278081371983443697082307530000000000000)
      constant := (50173917939731821851451901826259679306928522262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598714668338204366961/100000000000000000000)
  centralHi := (299357334169102183481/50000000000000000000)
  directionLo := (300394971021031204211/50000000000000000000)
  directionHi := (600789942042062408423/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree146.table
  base := (2988692306948416148537563530954827346271/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-57318805813922873811859446465543842250000000000000)
      constant := (2307167810073238804237650803503393047566681103477550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree146.table
  base := (14943461534741630447970230766834419637097/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1263716538696231495592274896026250000000000000)
      constant := (50878692835777949821249778858118612704251235530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300394971021031204211/50000000000000000000)
  centralHi := (600789942042062408423/100000000000000000000)
  directionLo := (75357258985374478093/12500000000000000000)
  directionHi := (120571614376599164949/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree147.table
  base := (152422450866821512780097329062566304796117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-6412355981169364581273562730552056770000000000000)
      constant := (259927858740917006322123147968164710810871758149853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree147.table
  base := (152422450866817703475226638563425266667273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1272367799311091007740852709744970000000000000)
      constant := (51588399664015358600452285864260505878073608577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75357258985374478093/12500000000000000000)
  centralHi := (120571614376599164949/20000000000000000000)
  directionLo := (30245956556623482583/5000000000000000000)
  directionHi := (604919131132469651661/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree148.table
  base := (3885963153025202233503565019837644614023/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-58103601847125688651064682684393179610000000000000)
      constant := (2371757296473279274754606437563560427091133400666520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree148.table
  base := (155438526121004866975747517802269835722923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1281019059925950519889430523463690000000000000)
      constant := (52303038424444058496467535131660867349191745427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30245956556623482583/5000000000000000000)
  centralHi := (604919131132469651661/100000000000000000000)
  directionLo := (606973191817925898837/100000000000000000000)
  directionHi := (303486595908962949419/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree149.table
  base := (158482841109981810751135605411680752012291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-58495999863727096070667300793817848290000000000000)
      constant := (2404387513488318119372704918368022728530334422209171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree149.table
  base := (39620710277494771253660145351925247470381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1289670320540810032038008337182410000000000000)
      constant := (53022609117064064278887644317144998633153568276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606973191817925898837/100000000000000000000)
  centralHi := (303486595908962949419/50000000000000000000)
  directionLo := (609020324752154162837/100000000000000000000)
  directionHi := (304510162376077081419/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree150.table
  base := (161555395833744268096188241301169501381029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-6543155320036500387807768767026946330000000000000)
      constant := (270804597745930046356577447999090611718530772546861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree150.table
  base := (10097212239608872659435279406018901342723/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1298321581155669544186586150901130000000000000)
      constant := (53747111741875394322888875802856666423565370032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609020324752154162837/100000000000000000000)
  centralHi := (304510162376077081419/50000000000000000000)
  directionLo := (611060599561776666201/100000000000000000000)
  directionHi := (305530299780888333101/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree151.table
  base := (20582023786537163378292189114266698329483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-59280795896929910909872537012667185650000000000000)
      constant := (2470318895148437126950012166976720613638902700679384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree151.table
  base := (20582023786536919622892573374169361551909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1306972841770529056335163964619850000000000000)
      constant := (54476546298878069893825756219438410163262449128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611060599561776666201/100000000000000000000)
  centralHi := (305530299780888333101/50000000000000000000)
  directionLo := (306547042357440070433/50000000000000000000)
  directionHi := (613094084714880140867/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree152.table
  base := (268456359177028760473688871414142602549/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-59673193913531318329475155122091854330000000000000)
      constant := (2503620059793519312259602545214530294881585535543125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree152.table
  base := (167785224485641326010421786202977437003493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1315624102385388568483741778338570000000000000)
      constant := (55210912788072114550297031507267088676252991357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306547042357440070433/50000000000000000000)
  centralHi := (613094084714880140867/100000000000000000000)
  directionLo := (307560423773912790439/50000000000000000000)
  directionHi := (615120847547825580879/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree153.table
  base := (34188499682756695805904375868004267335189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-6673954658903636194341974803501835890000000000000)
      constant := (281904985960957568784927443672221248167392190191505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree153.table
  base := (170942498413782084175300659083427391462231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1324275363000248080632319592057290000000000000)
      constant := (55950211209457553646599699340223790204851082719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307560423773912790439/50000000000000000000)
  centralHi := (615120847547825580879/100000000000000000000)
  directionLo := (308570477145632782381/50000000000000000000)
  directionHi := (617140954291265564763/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree154.table
  base := (21766001509590143288771855840247968294789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-60457989946734133168680391340941191690000000000000)
      constant := (2570893336713734756639883223456791190940582913858472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree154.table
  base := (1360375094349374739741985134328659877399/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1332926623615107592780897405776010000000000000)
      constant := (56694441563034413918543854929771669847851667328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308570477145632782381/50000000000000000000)
  centralHi := (617140954291265564763/100000000000000000000)
  directionLo := (123830894019079517627/20000000000000000000)
  directionHi := (77394308761924698517/12500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree155.table
  base := (35468353094891679382296576874567098315601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-60850387963335540588283009450365860370000000000000)
      constant := (2604865448988870481888372039237487253462091323766405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree155.table
  base := (88670882737228699675124110756662960233417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1341577884229967104929475219494730000000000000)
      constant := (57443603848802723139168723554992718463424782466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123830894019079517627/20000000000000000000)
  centralHi := (77394308761924698517/12500000000000000000)
  directionLo := (12423229181089612973/2000000000000000000)
  directionHi := (621161459054480648651/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree156.table
  base := (180583758606997717176253395270555066595123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-6804753997770772000876180839976725450000000000000)
      constant := (293229023386002954032229416262818804485493166227307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree156.table
  base := (90291879303498436806331685371855874946637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1350229144844826617078053033213450000000000000)
      constant := (58197698066762509833057194553691995824528094026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12423229181089612973/2000000000000000000)
  centralHi := (621161459054480648651/100000000000000000000)
  directionLo := (623161984230641184711/100000000000000000000)
  directionHi := (77895248028830148089/12500000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree157.table
  base := (36770798294868327842177607439097702684983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-61635183996538355427488245669215197730000000000000)
      constant := (2673480621169204385096181815999153464336217815902115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree157.table
  base := (183853991474340925900878100440355052909307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1358880405459686129226630846932170000000000000)
      constant := (58956724216913803039758081728420175000758655843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623161984230641184711/100000000000000000000)
  centralHi := (77895248028830148089/12500000000000000000)
  directionLo := (625156107676993383563/100000000000000000000)
  directionHi := (156289026919248345891/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree158.table
  base := (187152464076492723694640303777248793063143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-62027582013139762847090863778639866410000000000000)
      constant := (2708123681074405208399531033653005317845923381347383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree158.table
  base := (187152464076492120550292503521464412310453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1367531666074545641375208660650890000000000000)
      constant := (59720682299256632118347380742997826056542376397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625156107676993383563/100000000000000000000)
  centralHi := (156289026919248345891/25000000000000000000)
  directionLo := (313571945230048920141/50000000000000000000)
  directionHi := (627143890460097840283/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree159.table
  base := (190479176413453545716201158283449136321653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-6935553336637907807410386876451615010000000000000)
      constant := (304776710021070043753067743676067095445614636798077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree159.table
  base := (19047917641345303574356274273125609783953/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1376182926689405153523786474369610000000000000)
      constant := (60489572313791026586438322004683481064164778970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313571945230048920141/50000000000000000000)
  centralHi := (627143890460097840283/100000000000000000000)
  directionLo := (629125392681781564123/100000000000000000000)
  directionHi := (157281348170445391031/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree160.table
  base := (193834128485226683144248522387255235307299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-62812378046342577686296099997489203770000000000000)
      constant := (2778080748514881280251922827040384529541250256541619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree160.table
  base := (96917064242613125983730709152312474889837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1384834187304264665672364288088330000000000000)
      constant := (61263394260517015988023965013566451050027487626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629125392681781564123/100000000000000000000)
  centralHi := (157281348170445391031/25000000000000000000)
  directionLo := (631100673500341390023/100000000000000000000)
  directionHi := (78887584187542673753/12500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree161.table
  base := (98608660145907353558908815995529973075569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-63204776062943985105898718106913872450000000000000)
      constant := (2813394756050159203348399314752886997834912789126978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree161.table
  base := (197217320291814342576329498579415521365619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1393485447919124177820942101807050000000000000)
      constant := (62042148139434629785438159516146718304114971931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631100673500341390023/100000000000000000000)
  centralHi := (78887584187542673753/12500000000000000000)
  directionLo := (158267447787787989581/25000000000000000000)
  directionHi := (25322791646046078333/4000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree162.table
  base := (40125750366644034861778760313275808147113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-7066352675505043613944592912926504570000000000000)
      constant := (316548045866162832342039212194970598318540059256085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree162.table
  base := (4012575036664397322330908965607438211837/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1402136708533983689969519915525770000000000000)
      constant := (62825833950543897271478392555057878004366090650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158267447787787989581/25000000000000000000)
  centralHi := (25322791646046078333/4000000000000000000)
  directionLo := (79379100370837321583/12500000000000000000)
  directionHi := (127006560593339714533/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree163.table
  base := (51017105777361405166380900669980970057361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-63989572096146799945103954325763209810000000000000)
      constant := (2884693718750801460688468475287970243188112303727364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree163.table
  base := (102034211554722680061011284111799067071219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1410787969148843202118097729244490000000000000)
      constant := (63614451693844847498370437511343505037796772662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79379100370837321583/12500000000000000000)
  centralHi := (127006560593339714533/20000000000000000000)
  directionLo := (636989765396054432297/100000000000000000000)
  directionHi := (318494882698027216149/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree164.table
  base := (41507266824098711278137512181564120387993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-64381970112748207364706572435187878490000000000000)
      constant := (2920678673916168416052679431001811113515904001101165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree164.table
  base := (41507266824098667227486134325289158578863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1419439229763702714266675542963210000000000000)
      constant := (64408001369337509220789219076529057882847012435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636989765396054432297/100000000000000000000)
  centralHi := (318494882698027216149/50000000000000000000)
  directionLo := (31947036701191047941/5000000000000000000)
  directionHi := (638940734023820958821/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree165.table
  base := (211032484866366461951607761906696352299291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-7197152014372179420478798949401394130000000000000)
      constant := (328543030921285293955475963978337167784159371184019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree165.table
  base := (211032484866366275765046459672564955987017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1428090490378562226415253356681930000000000000)
      constant := (65206482977021910850599203202466146181095357633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31947036701191047941/5000000000000000000)
  centralHi := (638940734023820958821/100000000000000000000)
  directionLo := (40055360224284324777/6250000000000000000)
  directionHi := (640885763588549196433/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree166.table
  base := (42911375069413356989455827161021249284657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-65166766145951022203911808654037215850000000000000)
      constant := (2993319531877000420683846362174933105248254318522085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree166.table
  base := (107278437673533313782032075956453248400163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1436741750993421738563831170400650000000000000)
      constant := (66009896516898080421354604508793606481866932374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40055360224284324777/6250000000000000000)
  centralHi := (640885763588549196433/100000000000000000000)
  directionLo := (642824908000659557627/100000000000000000000)
  directionHi := (160706227000164889407/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree167.table
  base := (13631844097662308605613965994873636597463/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-65559164162552429623514426763461884530000000000000)
      constant := (3029975434672467994332883375257634211371332103988848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree167.table
  base := (218109505562596804658848719304590723366079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1445393011608281250712408984119370000000000000)
      constant := (66818241988966045560916277547999509191818238471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642824908000659557627/100000000000000000000)
  centralHi := (160706227000164889407/25000000000000000000)
  directionLo := (128951644071975302179/20000000000000000000)
  directionHi := (40297388772492281931/6250000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree168.table
  base := (221690375512959295378618636479524798185867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8426303714)
      previous := (4213151857)
      next := (4213151857)
      square := (40933136046203751572674922879817760000000000000)
      linear := (-7327951353239315227013004985876283690000000000000)
      constant := (340761665186441288921716655160251139258141586057603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree168.table
  base := (11084518775647959146791624097616247052897/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1454044272223140762860986797838090000000000000)
      constant := (67631519393225833470807985952962648250172355060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell209.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128951644071975302179/20000000000000000000)
  centralHi := (40297388772492281931/6250000000000000000)
  directionLo := (646685752972194162019/100000000000000000000)
  directionHi := (32334287648609708101/5000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree169.table
  base := (112649742599078097382882764861403992403439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (75836733426)
      previous := (37918366713)
      next := (37918366713)
      square := (368398224415833764154074305918359840000000000000)
      linear := (-66343960195755244462719662982311221890000000000000)
      constant := (3103958187893512452349944247484058711736239486145918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree169.table
  base := (225299485198156099728250948087723481572163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (1671554)
      previous := (835777)
      next := (835777)
      square := (8120042857806735086823035683360000000000000)
      linear := (-1462695532838000275009564611556810000000000000)
      constant := (68449728729677470911157943057426776140519694187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell209.Kernel169
