import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell140.Parameters
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch100_149
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch150_199
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch000_049
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch050_099
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch100_149
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree000.table
  base := (143866096329949122758478097/2000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (90564157728094656779616045000000000000)
      linear := (-6861863946304850615798276375000000000)
      constant := (89916310206218201724048810625000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree000.table
  base := (143866096329949122758478097/2000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (90564157728094656779616045000000000000)
      linear := (-6861863946304850615798276375000000000)
      constant := (89916310206218201724048810625000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree001.table
  base := (80765003905433013112622418636180251681699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-102525142197858420839595688043145634000000000000)
      constant := (50531023204795254700449496226305659679242087959055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree001.table
  base := (403741853593231632068378512521264421244943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-102550461672255252903264849198926509000000000000)
      constant := (50520636842280078553118498416928219773773315414127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49921412498889217363/100000000000000000000)
  directionHi := (12480353124722304341/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree002.table
  base := (15104570908180778059499994045578527067883/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-24773144350752197153665854240248136125000000000)
      constant := (3791470151512469629552879740677763157307982583574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree002.table
  base := (9663519045978213074167692764103710969997/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-198235793754811241356665156233546839000000000000)
      constant := (30321166736766537895205474251052789272037978788325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49921412498889217363/100000000000000000000)
  centralHi := (12480353124722304341/25000000000000000000)
  directionLo := (70599538608750872963/100000000000000000000)
  directionHi := (17649884652187718241/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree003.table
  base := (4845226546531062476209404672174180513319/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-36730645926772091702382247475103068000000000000)
      constant := (2453529930990558586376845111891830377281946085964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree003.table
  base := (154979457130577312119646577770220105615441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-293921125837367229810065463268167169000000000000)
      constant := (19619884555168655836119918078298912016543081969649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/100000000000000000000)
  centralHi := (17649884652187718241/25000000000000000000)
  directionLo := (86466422833680113569/100000000000000000000)
  directionHi := (8646642283368011357/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree004.table
  base := (106307397296257998989526052954034674675773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-389505180022335890008789125679663999000000000000)
      constant := (13713222860114803045155105579160081277983412059997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree004.table
  base := (53128539524081001588581319213393687996457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-194803228959961609131732885151393749500000000000)
      constant := (6853573901121407372708509635090533148412346230473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/100000000000000000000)
  centralHi := (8646642283368011357/10000000000000000000)
  directionLo := (49921412498889217363/50000000000000000000)
  directionHi := (99842824997778434727/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree005.table
  base := (77101634452869807051155068621596098976953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-485165192630495046398520271558503454000000000000)
      constant := (10291626772427069481491483810176410221669914957017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree005.table
  base := (77064539126137659706410767824808756120157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-485291790002479206716866077337407829000000000000)
      constant := (10287326632884201351295645075262363770612457019773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49921412498889217363/50000000000000000000)
  centralHi := (99842824997778434727/100000000000000000000)
  directionLo := (111627671880323934613/100000000000000000000)
  directionHi := (55813835940161967307/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree006.table
  base := (29183296705721776199175130364258733506057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-290412602619327101394125708718671454500000000000)
      constant := (4114995535383003841893879123776009058054666824873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree006.table
  base := (58338650779306964902514013937186044527989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-580977122085035195170266384372028159000000000000)
      constant := (8226983564036384249966771165156389209351550537621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111627671880323934613/100000000000000000000)
  centralHi := (55813835940161967307/50000000000000000000)
  directionLo := (4891279514451083249/4000000000000000000)
  directionHi := (61140993930638540613/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree007.table
  base := (45537252892866165709832448617397533915283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-676485217846813359177982563316182364000000000000)
      constant := (6957416526691610829503177731933621210399211270387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree007.table
  base := (22757765545051335344903362752826542846943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-338331227083795591811833345703324244500000000000)
      constant := (3477680865086287136975708929326085088700296792127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4891279514451083249/4000000000000000000)
  centralHi := (61140993930638540613/50000000000000000000)
  directionLo := (66039821284566193197/50000000000000000000)
  directionHi := (26415928513826477279/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree008.table
  base := (36246337634034320033084693579043250728751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-772145230454972515567713709195021819000000000000)
      constant := (6177852905477836295756046644505217199536477668239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree008.table
  base := (144915735128892160248687341464343922879/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-386173893125073586038533499220634409500000000000)
      constant := (3088269790565161691726097431012846372937893603875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66039821284566193197/50000000000000000000)
  centralHi := (26415928513826477279/20000000000000000000)
  directionLo := (70599538608750872963/50000000000000000000)
  directionHi := (141199077217501745927/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree009.table
  base := (14607725402944397977161042851022013694007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-433902621531565835978722427536930637000000000000)
      constant := (2865712276471658875959772297917381210432892782423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree009.table
  base := (7300294025691267353115147311061628167501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-217008279583175790132616826368972287250000000000)
      constant := (1432682691181867170198480554688539910135681466989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/50000000000000000000)
  centralHi := (141199077217501745927/100000000000000000000)
  directionLo := (149764237496667652089/100000000000000000000)
  directionHi := (14976423749666765209/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree010.table
  base := (23717329767415035952499103986165053994611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-963465255671290828347176000952700729000000000000)
      constant := (5527180374833984192850611983894122668473460413779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree010.table
  base := (11852719462935394985605950837870807877461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-481859225207629574491933806255254739500000000000)
      constant := (2763519826244392952544918887637623179297447277429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149764237496667652089/100000000000000000000)
  centralHi := (14976423749666765209/10000000000000000000)
  directionLo := (157865367509287880971/100000000000000000000)
  directionHi := (39466341877321970243/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree011.table
  base := (2414064742640598074840626192696792321781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-132390658534931248092113393353942523000000000000)
      constant := (688770269516433186388837145786060216275274179909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree011.table
  base := (9651263008752685478377155412040670845807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-529701891248907568718633959772564904500000000000)
      constant := (2755270293907577355291318974217259207068821212623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157865367509287880971/100000000000000000000)
  centralHi := (39466341877321970243/25000000000000000000)
  directionLo := (2069632428292173603/1250000000000000000)
  directionHi := (165570594263373888241/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree012.table
  base := (15718438131497801406495797344968836430613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1154785280887609141126638292710379639000000000000)
      constant := (5645030937160947282300497878350127744187045736757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree012.table
  base := (3142001883723342824089047032283368875349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1155089114580371125890668226579750139000000000000)
      constant := (5645913274468206765919286548718359844248253183305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2069632428292173603/1250000000000000000)
  centralHi := (165570594263373888241/100000000000000000000)
  directionLo := (86466422833680113569/50000000000000000000)
  directionHi := (172932845667360227139/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree013.table
  base := (12742774963688433827242342225980563543439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1250445293495768297516369438589219094000000000000)
      constant := (5907735855417388804824411645095802686893260642671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree013.table
  base := (1591957486666703985374970079179441781761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-156346805832865889293008566701796308625000000000)
      constant := (738639702804878860326408154885689994094780180129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/50000000000000000000)
  centralHi := (172932845667360227139/100000000000000000000)
  directionLo := (44998553127083488661/25000000000000000000)
  directionHi := (35998842501666790929/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree014.table
  base := (10248426871540628871510197227794559047569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1346105306103927453906100584468058549000000000000)
      constant := (6281131059096214377564342941328622484969305832241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree014.table
  base := (10242427729561888673130519493101925539087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1346459778745483102797468840648990799000000000000)
      constant := (6283014264765524840267752736936659622584269746543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44998553127083488661/25000000000000000000)
  centralHi := (35998842501666790929/20000000000000000000)
  directionLo := (93394410917328902051/50000000000000000000)
  directionHi := (186788821834657804103/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree015.table
  base := (8134214469471125808641616084155610789033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1441765318712086610295831730346898004000000000000)
      constant := (6752563105939047446590467385099052362853103784137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree015.table
  base := (8129167276291837817404758481160932860429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1442145110828039091250869147683611129000000000000)
      constant := (6754953978017849891838699043806253356538559060781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93394410917328902051/50000000000000000000)
  centralHi := (186788821834657804103/100000000000000000000)
  directionLo := (193344799227348726231/100000000000000000000)
  directionHi := (24168099903418590779/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree016.table
  base := (3161825739879633961689874086743051339119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-768712665660122883342781438112868729500000000000)
      constant := (3656233330569315299174172366961631639270987850191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree016.table
  base := (6319416477933318126741156800984853465503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1537830442910595079704269454718231459000000000000)
      constant := (7315374456596010885589961801422967725135684307967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193344799227348726231/100000000000000000000)
  centralHi := (24168099903418590779/12500000000000000000)
  directionLo := (199685649995556869453/100000000000000000000)
  directionHi := (99842824997778434727/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree017.table
  base := (951598215769176979283568737350501353639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1633085343928404923075294022104576914000000000000)
      constant := (7953494876960280831441506022432674643118258152355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree017.table
  base := (1188611898298550099722595874334114313081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-408378943748287767039417440438212947250000000000)
      constant := (1989232809795972485941565507483238214511495875609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199685649995556869453/100000000000000000000)
  centralHi := (99842824997778434727/50000000000000000000)
  directionLo := (102915628356474962727/50000000000000000000)
  directionHi := (41166251342589985091/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree018.table
  base := (3391649665638637665594631866006181956889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1728745356536564079465025167983416369000000000000)
      constant := (8669947091544610380941323494047586712119558369721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree018.table
  base := (1694346542399875112641418322650290720273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-864600553537853528305535034393736059500000000000)
      constant := (4336962836427460164310584045836451064803783320497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102915628356474962727/50000000000000000000)
  centralHi := (41166251342589985091/20000000000000000000)
  directionLo := (211798615826252618889/100000000000000000000)
  directionHi := (21179861582625261889/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree019.table
  base := (218903093338827408031460835226616105651/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-912202684572361617927378156931127912000000000000)
      constant := (4728685824479635260881086163968283584156295361695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree019.table
  base := (2186570675622728954615645398352006155371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1824886439158263045064470375822092449000000000000)
      constant := (9461907856214113186441693774343374116665551865419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211798615826252618889/100000000000000000000)
  centralHi := (21179861582625261889/10000000000000000000)
  directionLo := (217602392201466385667/100000000000000000000)
  directionHi := (54400598050366596417/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree020.table
  base := (1122227747067171398394855825586694040617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1920065381752882392244487459741095279000000000000)
      constant := (10312278497158252752881878139537951005668907264713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree020.table
  base := (224037133790944457525335447675784006317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-1920571771240819033517870682856712779000000000000)
      constant := (10317389292745304242961823708179022445021883960065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217602392201466385667/100000000000000000000)
  centralHi := (54400598050366596417/25000000000000000000)
  directionLo := (223255343760647869227/100000000000000000000)
  directionHi := (55813835940161967307/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree021.table
  base := (169308192125418242068404671926566237299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2015725394361041548634218605619934734000000000000)
      constant := (11231924842115153492401617747841216692380015680211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree021.table
  base := (41904300630747571007371408328723732857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-504064275830843755492817747472833277250000000000)
      constant := (2809407142653556315654861094063449374428268930073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223255343760647869227/100000000000000000000)
  centralHi := (55813835940161967307/25000000000000000000)
  directionLo := (228768651575274412739/100000000000000000000)
  directionHi := (11438432578763720637/5000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree022.table
  base := (-17174731218070331088623774063025169177/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-263923175871150088127993718937346773625000000000)
      constant := (1526768995912355305231013306569309883117929147235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree022.table
  base := (-688386460773590502097498398350518583333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2111942435405931010424671296925953439000000000000)
      constant := (12220468196394647405941685227661752019833371103163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228768651575274412739/100000000000000000000)
  centralHi := (11438432578763720637/5000000000000000000)
  directionLo := (234152179937436321573/100000000000000000000)
  directionHi := (117076089968718160787/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree023.table
  base := (-182532807214292064183666471570916436393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-275880677447169982676710112172201705500000000000)
      constant := (1657157416063162691693462904613788897339709166823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree023.table
  base := (-730707303704811862151516680344485076129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-1103813883744243499439035801980286884500000000000)
      constant := (6632104350432091064269102743649640544036181161919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234152179937436321573/100000000000000000000)
  centralHi := (117076089968718160787/50000000000000000000)
  directionLo := (59853670937617628087/25000000000000000000)
  directionHi := (239414683750470512349/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree024.table
  base := (-2161229101110212304651777789038084107817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2302705432185519017803412043256453099000000000000)
      constant := (14359906579868649971139847854591109723437385074487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree024.table
  base := (-540544351466205808611815641646906200973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-575828274892760746832867977748798524750000000000)
      constant := (3591877668956413127307288483247487182325385317203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59853670937617628087/25000000000000000000)
  centralHi := (239414683750470512349/100000000000000000000)
  directionLo := (244563975722554162451/100000000000000000000)
  directionHi := (61140993930638540613/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree025.table
  base := (-699584872272494091966258884457509965477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-599591361198419543548285797283823138500000000000)
      constant := (3880259232478985878843917317485424680059726238747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree025.table
  base := (-349889834330129038530141765260662170723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-299874803956699871973109027253726803625000000000)
      constant := (1941164767706501160299504160360877868377750859453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244563975722554162451/100000000000000000000)
  centralHi := (61140993930638540613/25000000000000000000)
  directionLo := (7800220702951440213/3125000000000000000)
  directionHi := (249607062494446086817/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree026.table
  base := (-675651515122576962923841974218641906553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2494025457401837330582874335014132009000000000000)
      constant := (16739816987970318070129586751815777269712480342915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree026.table
  base := (-1689448392849580869441903864525775406393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-1247341881868077482119136262532217379500000000000)
      constant := (8374399202874124508133385974722651925472724086823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7800220702951440213/3125000000000000000)
  centralHi := (249607062494446086817/100000000000000000000)
  directionLo := (254550256477950866183/100000000000000000000)
  directionHi := (31818782059743858273/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree027.table
  base := (-3906239222729353152660379001923790356707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2589685470009996486972605480892971464000000000000)
      constant := (18015589458609494179765200217129501837640844857277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree027.table
  base := (-97669070777110418381609565711940903993/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-323796136977338869086459104012381886125000000000)
      constant := (2253161846153313297814695115489517216960936802115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254550256477950866183/100000000000000000000)
  centralHi := (31818782059743858273/12500000000000000000)
  directionLo := (259399268501040340707/100000000000000000000)
  directionHi := (64849817125260085177/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree028.table
  base := (-4386430034210822571132289705839203682891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2685345482618155643362336626771810919000000000000)
      constant := (19347835894744218936374640346591265999500733497301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree028.table
  base := (-274178647564462231789251295365166006853/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-335756803487658367643134142391709427375000000000)
      constant := (2419786161491346834214733550584755214628086643766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259399268501040340707/100000000000000000000)
  centralHi := (64849817125260085177/25000000000000000000)
  directionLo := (264159285138264772789/100000000000000000000)
  directionHi := (26415928513826477279/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree029.table
  base := (-2411050016910939990111238422212684190181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-1390502747613157399876033886325325187000000000000)
      constant := (10368073674436737622336882568120724505966960322491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree029.table
  base := (-4822449971593202929504809362421143630829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2781739759983822929598473446168295749000000000000)
      constant := (20747373455027883252931483909705854093232920613619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264159285138264772789/100000000000000000000)
  centralHi := (26415928513826477279/10000000000000000000)
  directionLo := (268835033711462771163/100000000000000000000)
  directionHi := (67208758427865692791/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree030.table
  base := (-1303957165787061878868059266323111624273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-719166376958618489035449729632372457250000000000)
      constant := (5545050309337661836173947822233127734503458623503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree030.table
  base := (-5216114218537188039904196017688244914179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2877425092066378918051873753202916079000000000000)
      constant := (22192225035770187371044373004044075093475925405469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268835033711462771163/100000000000000000000)
  centralHi := (67208758427865692791/25000000000000000000)
  directionLo := (136715418640809838621/50000000000000000000)
  directionHi := (273430837281619677243/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree031.table
  base := (-5569650655739671890968321025581339348847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-2972325520442633112531530064408329284000000000000)
      constant := (23679743097437752756297600665811996458191351440817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree031.table
  base := (-2784941707643338172912433100387269325141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-1486555212074467453252637030118768204500000000000)
      constant := (11846294937039739062303785721624564856217491687051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136715418640809838621/50000000000000000000)
  centralHi := (273430837281619677243/100000000000000000000)
  directionLo := (138975330726726307889/50000000000000000000)
  directionHi := (277950661453452615779/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree032.table
  base := (-5885171080439575852018090619399042855707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3067985533050792268921261210287168739000000000000)
      constant := (25234572200045423209940077440464812551376181846277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree032.table
  base := (-294268030408165303695623253081672597509/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-767198939057872723739668591818039184750000000000)
      constant := (6312066873450482026838477165198128495451108935495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138975330726726307889/50000000000000000000)
  centralHi := (277950661453452615779/100000000000000000000)
  directionLo := (70599538608750872963/25000000000000000000)
  directionHi := (282398154435003491853/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree033.table
  base := (-3081828039548469311110784004496274506859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-1581822772829475712655496178083004097000000000000)
      constant := (13422265101060511924374093050445837653377861464949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree033.table
  base := (-246552410161953326923984077474321935391/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3164481088314046883412074674306777069000000000000)
      constant := (26859099762606042386887162437603270370462763120025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/25000000000000000000)
  centralHi := (282398154435003491853/100000000000000000000)
  directionLo := (286776681503535665221/100000000000000000000)
  directionHi := (143388340751767832611/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree034.table
  base := (-640610443811075389363767910371415533371/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-1629652779133555290850361751022423824500000000000)
      constant := (14254746097973938185739407007490063038324801462905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree034.table
  base := (-6406229739534486751737035266329629067691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3260166420396602871865474981341397399000000000000)
      constant := (28524961947834386399035061290427406140485017130101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286776681503535665221/100000000000000000000)
  centralHi := (143388340751767832611/50000000000000000000)
  directionLo := (72772338700937987093/25000000000000000000)
  directionHi := (291089354803751948373/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree035.table
  base := (-1653326011065222724328983136146608081291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-838741392718817434522613661980921776000000000000)
      constant := (7557339912201975119152521674595699438918914579701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree035.table
  base := (-6613405791444481811195410336293192040743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3355851752479158860318875288376017729000000000000)
      constant := (30245755661832341222900058020166863107955813239673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72772338700937987093/25000000000000000000)
  centralHi := (291089354803751948373/100000000000000000000)
  directionLo := (18458691201778436397/6250000000000000000)
  directionHi := (295339059228454982353/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree036.table
  base := (-1696469104551517835291681375356400898403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-862656395870857223620046448450631639750000000000)
      constant := (8001013708411278370989380655813856798954079903933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree036.table
  base := (-6785958971451417358520635927293294182529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3451537084561714848772275595410638059000000000000)
      constant := (32021403297474238641359083875186125847906250532319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18458691201778436397/6250000000000000000)
  centralHi := (295339059228454982353/100000000000000000000)
  directionLo := (299528474993335304179/100000000000000000000)
  directionHi := (14976423749666765209/5000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree037.table
  base := (-6924311843874686449394957972898296476659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3546285596091588050869916939681366014000000000000)
      constant := (33833516435801965874429972564468665300877275032749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree037.table
  base := (-865547346539157743698425298209460590221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-443402802080533854653209487805657298625000000000)
      constant := (4231480454880737238267047766592245243058823342931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299528474993335304179/100000000000000000000)
  centralHi := (14976423749666765209/5000000000000000000)
  directionLo := (75915024351951136527/25000000000000000000)
  directionHi := (303660097407804546109/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree038.table
  base := (-3514498539915571518065212016119445573281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-1820972804349873603629824042780102734500000000000)
      constant := (17858848043725013279132123247774295954642166086591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree038.table
  base := (-7029051301127559864400810358165190013989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3642907748726826825679076209479878719000000000000)
      constant := (35737028400191000856419641988549395090012632808379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75915024351951136527/25000000000000000000)
  centralHi := (303660097407804546109/100000000000000000000)
  directionLo := (61547250851228634807/20000000000000000000)
  directionHi := (76934063564035793509/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree039.table
  base := (-7100237219136290124247875043259501272401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3737605621307906363649379231439044924000000000000)
      constant := (37656555633807008310753478699934810993572431136911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree039.table
  base := (-1775070278867453142034979605484196873501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-934648270202345703533119129128624762250000000000)
      constant := (9419229873273696050013704770864463885737067299011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61547250851228634807/20000000000000000000)
  centralHi := (76934063564035793509/25000000000000000000)
  directionLo := (31175912113278394083/10000000000000000000)
  directionHi := (311759121132783940831/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree040.table
  base := (-1427654586670272719469834423385587589383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-3833265633916065520039110377317884379000000000000)
      constant := (39650064976610446140085956947640715803035100973565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree040.table
  base := (-3569154223732309162367454983032127945803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-1917139206445969401292938411774559689500000000000)
      constant := (19835743437225252146912258775574744176015257125333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31175912113278394083/10000000000000000000)
  centralHi := (311759121132783940831/100000000000000000000)
  directionLo := (315730735018575761943/100000000000000000000)
  directionHi := (39466341877321970243/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree041.table
  base := (-1785823518844716189120694081549287123083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-982231411631056169107210380799180958500000000000)
      constant := (10424550093238342016682681383161604756127647415413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree041.table
  base := (-1785830697485077764477652679606416464079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-982490936243623697759819282645934927250000000000)
      constant := (10430176711595470133126586427370452236881093404369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315730735018575761943/100000000000000000000)
  centralHi := (39466341877321970243/12500000000000000000)
  directionLo := (19978312896157543819/6250000000000000000)
  directionHi := (63930601267704140221/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree042.table
  base := (-5692360328002285499742105041120890147/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2012292829566191916409286334537781644500000000000)
      constant := (21900471546664204471209558641166274123994403198125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree042.table
  base := (-711547361304721634732503642101315751999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2012824538528525389746338718809180019500000000000)
      constant := (21912280358114146222962321657503662221261771657445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19978312896157543819/6250000000000000000)
  centralHi := (63930601267704140221/20000000000000000000)
  directionLo := (323527729703558189591/100000000000000000000)
  directionHi := (40440966212944773699/12500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree043.table
  base := (-7054860078633250035666338314689518416921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-4120245671740542989208303814954402744000000000000)
      constant := (45958278363031215672543585868963313573717520786631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree043.table
  base := (-1410975763484143968730175732541703048069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-4121334409139606767946077744652980369000000000000)
      constant := (45983033739396525929288351051365880803843742116295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323527729703558189591/100000000000000000000)
  centralHi := (40440966212944773699/12500000000000000000)
  directionLo := (163678296753893780143/50000000000000000000)
  directionHi := (327356593507787560287/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree044.table
  base := (-3480808138344221995881411101257330186497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2107952842174351072799017480416621099500000000000)
      constant := (24085097263545193021441012642453791227997410479967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree044.table
  base := (-870203925244463403568595571688784365693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-527127467652770344549934756460950087375000000000)
      constant := (6024514285686538626816946777282540570007744289123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163678296753893780143/50000000000000000000)
  centralHi := (327356593507787560287/100000000000000000000)
  directionLo := (2069632428292173603/625000000000000000)
  directionHi := (331141188526747776481/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree045.table
  base := (-1708948130256366418522568528644997448791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1077891424239215325496941526678020413500000000000)
      constant := (12609170597881336844842232762233529695202581372201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree045.table
  base := (-3417902361642333823632124080801336349861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2156352536652359372426439179361110514500000000000)
      constant := (25231896590286333924181928525952616661819258118971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2069632428292173603/625000000000000000)
  centralHi := (331141188526747776481/100000000000000000000)
  directionLo := (334883015640971803841/100000000000000000000)
  directionHi := (167441507820485901921/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree046.table
  base := (-1669361701283628085921172531981129572579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1101806427391255114594374313147730277250000000000)
      constant := (13189433675924962571507485470260604780885481847869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree046.table
  base := (-333872832220268219039976812476683527849/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1102097601346818683326569666439210339750000000000)
      constant := (13196515797080167536677025039800111322399933954195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334883015640971803841/100000000000000000000)
  centralHi := (167441507820485901921/50000000000000000000)
  directionLo := (338583492791180855561/100000000000000000000)
  directionHi := (169291746395590427781/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree047.table
  base := (-6486624876950427048032207494976301980989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-4502885722173179614767228398469760564000000000000)
      constant := (55133345742400540486051238721859966776241577945379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree047.table
  base := (-3243316403540098639307174713279870433821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2252037868734915360879839486395730844500000000000)
      constant := (27581459300400416562490596978585383566685137422531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338583492791180855561/100000000000000000000)
  centralHi := (169291746395590427781/50000000000000000000)
  directionLo := (171121980628264023549/50000000000000000000)
  directionHi := (342243961256528047099/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree048.table
  base := (-1565840706135883960543640086090908624651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1149636433695334692789239886087150004750000000000)
      constant := (14390877748617946001731479106896661766605453136661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree048.table
  base := (-6263369213074824117514326753655394818099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-4599761069552386710213079279826082019000000000000)
      constant := (57594354915650740523866949172532286643955291108589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171121980628264023549/50000000000000000000)
  centralHi := (342243961256528047099/100000000000000000000)
  directionLo := (86466422833680113569/25000000000000000000)
  directionHi := (345865691334720454277/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree049.table
  base := (-3003844557916707235437236001704662950041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2347102873694748963773345345113719737000000000000)
      constant := (30024113449865052906458577196329544815160015010951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree049.table
  base := (-6007694260215550103394487717998966186153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-4695446401634942698666479586860702349000000000000)
      constant := (60080368581452745903558094880573439347231426944183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/25000000000000000000)
  centralHi := (345865691334720454277/100000000000000000000)
  directionLo := (174724943746112260771/50000000000000000000)
  directionHi := (349449887492224521543/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree050.table
  base := (-1143925241522084587340964782475191904131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-4789865759997657083936421836106278929000000000000)
      constant := (62587490649740778901977149378900471770212200754705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree050.table
  base := (-5719630348412748926671506510048098704279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-4791131733717498687119879893895322679000000000000)
      constant := (62620956796885504284532077609956103641871306146569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174724943746112260771/50000000000000000000)
  centralHi := (349449887492224521543/100000000000000000000)
  directionLo := (22062355815234647801/6250000000000000000)
  directionHi := (352997693043754364817/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree051.table
  base := (-2699595907403532003514428219625068597653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2442762886302908120163076490992559192000000000000)
      constant := (32590650014541698404264184334253108550884444220683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree051.table
  base := (-5399195146477410682339179303925574936839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-4886817065800054675573280200929943009000000000000)
      constant := (65216117352296542007924911752974329317117707384729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22062355815234647801/6250000000000000000)
  centralHi := (352997693043754364817/100000000000000000000)
  directionLo := (14260407776503272559/4000000000000000000)
  directionHi := (44563774301572726747/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree052.table
  base := (-2523199955879254040837624475923391174567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2490592892606987698357942063931978919500000000000)
      constant := (33914826645067372003820155966096274127436541183737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree052.table
  base := (-630800323921799575568757283203365104507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-622812799735326333003335063495570417375000000000)
      constant := (8483231063092019414604696223462859090137422983077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14260407776503272559/4000000000000000000)
  centralHi := (44563774301572726747/12500000000000000000)
  directionLo := (359988425016667909289/100000000000000000000)
  directionHi := (35998842501666790929/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree053.table
  base := (-2330630761021816479476422526390069881129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3205512)
      previous := (1602756)
      next := (1602756)
      square := (16128027464850008857941143757780000000000000)
      linear := (-903674937312590700089999158729583000000000000)
      constant := (12554743512689868118665544700041938183197255791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree053.table
  base := (-466126367642420324317473399687366329847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3205512)
      previous := (1602756)
      next := (1602756)
      square := (16128027464850008857941143757780000000000000)
      linear := (-903913800278598549747255396048270500000000000)
      constant := (12561436254785564346656634502912466568144408565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359988425016667909289/100000000000000000000)
  centralHi := (35998842501666790929/10000000000000000000)
  directionLo := (181716684410007730583/50000000000000000000)
  directionHi := (363433368820015461167/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree054.table
  base := (-848757068309696527580972872030380358513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5172505810430293709495346419621636749000000000000)
      constant := (73289986234051136992844661712080825680443637100715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree054.table
  base := (-2121893536514616175575434178206644188249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2586936531023861320466740561016901999500000000000)
      constant := (36664508695901412139684016030521335953787760255239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181716684410007730583/50000000000000000000)
  centralHi := (363433368820015461167/100000000000000000000)
  directionLo := (366845963583831243677/100000000000000000000)
  directionHi := (183422981791915621839/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree055.table
  base := (-3793978229967768996453594712013356878441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5268165823038452865885077565500476204000000000000)
      constant := (76101963971543202350730014995190590268701283423351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree055.table
  base := (-237123726317856739764956919001388456161/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-658694799266284828673360178633553041125000000000)
      constant := (9517806648324350010182074137950570095170262876542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366845963583831243677/100000000000000000000)
  centralHi := (183422981791915621839/50000000000000000000)
  directionLo := (370227103847940732513/100000000000000000000)
  directionHi := (185113551923970366257/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree056.table
  base := (-206990349907759326145840266281278395019/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-670478229455826502784351088922414457375000000000)
      constant := (9871060198755391848962385722367668299991867429418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree056.table
  base := (-3311846715816029215335743738899162117571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5365243726212834617840281736103044659000000000000)
      constant := (79010455589037471580845834820379971352048412818781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370227103847940732513/100000000000000000000)
  centralHi := (185113551923970366257/50000000000000000000)
  directionLo := (74715528733863121641/20000000000000000000)
  directionHi := (186788821834657804103/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree057.table
  base := (-2797391715819232909346514590711337962791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5459485848254771178664539857258155114000000000000)
      constant := (81889538555721798273872771803974630190085806526201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree057.table
  base := (-2797392612898511971381882716965680510113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5460929058295390606293682043137664989000000000000)
      constant := (81933024066917883294858278084679850202868008887743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74715528733863121641/20000000000000000000)
  centralHi := (186788821834657804103/50000000000000000000)
  directionLo := (376898399141469419819/100000000000000000000)
  directionHi := (18844919957073470991/5000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree058.table
  base := (-2250619949103071708367662253373318538273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5555145860862930335054271003136994569000000000000)
      constant := (84865134447472622004069770975108181580619351677503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree058.table
  base := (-1125310334575427411182832008989967763941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2778307195188973297373541175086142659500000000000)
      constant := (42455079100217064577833198232343565624440065913851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376898399141469419819/100000000000000000000)
  centralHi := (18844919957073470991/5000000000000000000)
  directionLo := (380190150715778865859/100000000000000000000)
  directionHi := (19009507535788943293/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree059.table
  base := (-835766477299365602502786104287032813769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2825402936735544745722001074507917012000000000000)
      constant := (43947634466554853364820068720635725609280691695959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree059.table
  base := (-835766766189489122305681974985288075427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2826149861230251291600241328603452824500000000000)
      constant := (43970928829226476888663219683512472525644305923197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380190150715778865859/100000000000000000000)
  centralHi := (19009507535788943293/5000000000000000000)
  directionLo := (11982926416982428163/3125000000000000000)
  directionHi := (383453645343437701217/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree060.table
  base := (-1060132827639133314537948346407917723393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5746465886079248647833733294894673479000000000000)
      constant := (90979941750591787950982340260875928970208428073823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree060.table
  base := (-1060133291127975622120913707695684544947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5747985054543058571653882964241525979000000000000)
      constant := (91028122179781975027777844501463686375803730647917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11982926416982428163/3125000000000000000)
  centralHi := (383453645343437701217/100000000000000000000)
  directionLo := (193344799227348726231/50000000000000000000)
  directionHi := (386689598454697452463/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree061.table
  base := (-104105305275485617290636986646698065029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1460531474671851951055866110193378233500000000000)
      constant := (23529788173302707393673063190393703093504871989819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree061.table
  base := (-208210796402110471322617409588548766447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2921835193312807280053641635638073154500000000000)
      constant := (47084475779198696800384794681214922564266557834417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193344799227348726231/50000000000000000000)
  centralHi := (386689598454697452463/100000000000000000000)
  directionLo := (15595947831610076631/4000000000000000000)
  directionHi := (761520890215335773/195312500000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree062.table
  base := (129800280581764694600489257045742170209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-2968892955647783480306597793326176194500000000000)
      constant := (48656450798954051458155902887840579450682088563201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree062.table
  base := (259600263151062262078531472365904430091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-5939355718708170548560683578310766639000000000000)
      constant := (97364345631791754095887851783725593380800016683499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15595947831610076631/4000000000000000000)
  centralHi := (761520890215335773/195312500000000000)
  directionLo := (393081595098045336557/100000000000000000000)
  directionHi := (196540797549022668279/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree063.table
  base := (967931490636878499759347666289855623139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6033445923903726117002926732531191844000000000000)
      constant := (100561188336057371855442513050393478003207289915971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree063.table
  base := (241982812941851833405636891081443660511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1508760262697681634253520971336346742250000000000)
      constant := (25153576067945693428184527212848461568628295138879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393081595098045336557/100000000000000000000)
  centralHi := (196540797549022668279/50000000000000000000)
  directionLo := (396238927707397159183/100000000000000000000)
  directionHi := (24764932981712322449/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree064.table
  base := (1708570755989104214319480772128496045413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6129105936511885273392657878410031299000000000000)
      constant := (103864012806194246160140679385415753753777870573957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree064.table
  base := (1708570564573460572431970402238107701409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6130726382873282525467484192380007299000000000000)
      constant := (103918827377263438086515772365568086101465174120001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396238927707397159183/100000000000000000000)
  centralHi := (24764932981712322449/6250000000000000000)
  directionLo := (199685649995556869453/50000000000000000000)
  directionHi := (399371299991113738907/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree065.table
  base := (1240758858610542597936015600613561148467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3112382974560022214891194512144435377000000000000)
      constant := (53610687464140381377775459551464378023306911153363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree065.table
  base := (24815175638695364718962603684796776807/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1556602928738959628480221124853656907250000000000)
      constant := (26819478717120837603075855529913524208158261790575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199685649995556869453/50000000000000000000)
  centralHi := (399371299991113738907/100000000000000000000)
  directionLo := (402479294725177654427/100000000000000000000)
  directionHi := (100619823681294413607/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree066.table
  base := (164338593474295987346304972186120158293/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1580106490432050896543030042541927552250000000000)
      constant := (27658318659795256523037946932019656555131108461385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree066.table
  base := (82169293666457038599476587374804225533/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-790262130879799312796785600806155994875000000000)
      constant := (13836445835317239836816858009122922900257238663185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402479294725177654427/100000000000000000000)
  centralHi := (100619823681294413607/25000000000000000000)
  directionLo := (25347717022165603043/6250000000000000000)
  directionHi := (405563472354649648689/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree067.table
  base := (2062166407275173626404651016499782649487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3208042987168181371280925658023274832000000000000)
      constant := (57049855944546094047334265541059236080052785332143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree067.table
  base := (4124332716193562303820317639160403520669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6417782379120950490827685113483868289000000000000)
      constant := (114159782769810274216867709617492245900078666078141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25347717022165603043/6250000000000000000)
  centralHi := (405563472354649648689/100000000000000000000)
  directionLo := (408624372173570824601/100000000000000000000)
  directionHi := (204312186086785412301/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree068.table
  base := (2497100119141115244759987845543363972989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3255872993472260949475791230962694559500000000000)
      constant := (58810343319364522101694811310177532751178014142621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree068.table
  base := (4994200159538535400556564463103854253693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6513467711203506479281085420518488619000000000000)
      constant := (117682563091164695260569926944672556886397322942877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408624372173570824601/100000000000000000000)
  centralHi := (204312186086785412301/50000000000000000000)
  directionLo := (102915628356474962727/25000000000000000000)
  directionHi := (411662513425899850909/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree069.table
  base := (2948186946445836604972810191368545464699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3303702999776340527670656803902114287000000000000)
      constant := (60598099428551558307144077681433979714097899478811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree069.table
  base := (5896373829863702455747682548126842768411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6609153043286062467734485727553108949000000000000)
      constant := (121259907615732810888307465852804279567300825001979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102915628356474962727/25000000000000000000)
  centralHi := (411662513425899850909/100000000000000000000)
  directionLo := (25917399770865613429/6250000000000000000)
  directionHi := (82935679266769962973/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree070.table
  base := (6830853582922024419834078604221398879111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6703066012160840211731044753683068029000000000000)
      constant := (124826248519770696432371612555093257666686794434279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree070.table
  base := (1707713383120954617179105422947638202783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1676209593842154614046971508646932319750000000000)
      constant := (31222954079791845961113956194411317257084420357887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25917399770865613429/6250000000000000000)
  centralHi := (82935679266769962973/20000000000000000000)
  directionLo := (52209062882423979133/12500000000000000000)
  directionHi := (83534500611878366613/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree071.table
  base := (3898819577099482864881172435638881888349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3399363012384499684060387949780953742000000000000)
      constant := (64255417803725411091467725063162485480035155993661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree071.table
  base := (1949409778460992723150051999330645986241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-1700130926862793611160321585405587402250000000000)
      constant := (32144572295566228808116170418610107530391700490849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52209062882423979133/12500000000000000000)
  centralHi := (83534500611878366613/20000000000000000000)
  directionLo := (84129059720831762717/20000000000000000000)
  directionHi := (210322649302079406793/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree072.table
  base := (8796730485113070268911244863106799719829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6894386037377158524510507045440746939000000000000)
      constant := (132249960104935081083932153124602006035887157907381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree072.table
  base := (549795653301995932670693607891958064749/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-862026129941716304136835831082121242375000000000)
      constant := (16539915773734896513326142335572281900948877706522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84129059720831762717/20000000000000000000)
  centralHi := (210322649302079406793/50000000000000000000)
  directionLo := (423597231652505237779/100000000000000000000)
  directionHi := (21179861582625261889/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree073.table
  base := (9828127479743110583397166693771185644333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6990046049985317680900238191319586394000000000000)
      constant := (136043622000227613445726265981994715235823170725837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree073.table
  base := (9828127453925471727016851899895601356049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-6991894371616286421548086955691590269000000000000)
      constant := (136114927330064192090411783600511489610935194998961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423597231652505237779/100000000000000000000)
  centralHi := (21179861582625261889/5000000000000000000)
  directionLo := (26658045960128180369/6250000000000000000)
  directionHi := (85305747072410177181/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree074.table
  base := (10891830062431433092236118643870123881679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7085706062593476837289969337198425849000000000000)
      constant := (139891821283866711772540910576894603417259472202031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree074.table
  base := (5445915020893505300929126295061044196717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3543789851849421205000743631363105299500000000000)
      constant := (69982546296699148544589563883677823057172843497613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26658045960128180369/6250000000000000000)
  centralHi := (85305747072410177181/20000000000000000000)
  directionLo := (107360057026413078153/25000000000000000000)
  directionHi := (429440228105652312613/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree075.table
  base := (11987838173504788398645606048513625979677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7181366075201635993679700483077265304000000000000)
      constant := (143794557948389669987844909882365302383149280005053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree075.table
  base := (2397567631400002442073946319382606139109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7183265035781398398454887569760830929000000000000)
      constant := (143869821972450885055291863174539352739976172276505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107360057026413078153/25000000000000000000)
  centralHi := (429440228105652312613/100000000000000000000)
  directionLo := (86466422833680113569/20000000000000000000)
  directionHi := (216166057084200283923/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree076.table
  base := (2623230353179749751480047761123359802111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7277026087809795150069431628956104759000000000000)
      constant := (147751831987910634807742954422414417589325713906395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree076.table
  base := (6558075876352938725399700388390365548447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3639475183931977193454143938397725629500000000000)
      constant := (73914557730680921764914519843026439701261986563583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/20000000000000000000)
  centralHi := (216166057084200283923/50000000000000000000)
  directionLo := (217602392201466385667/50000000000000000000)
  directionHi := (87040956880586554267/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree077.table
  base := (7138385401247457753659192474210406205727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3686343050208977153229581387417472107000000000000)
      constant := (75881821698893799131584692583546512349680022493503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree077.table
  base := (2855354158390239332156094380717222511181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7374635699946510375361688183830071589000000000000)
      constant := (151842973055509797983607404235764056684237963232545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217602392201466385667/50000000000000000000)
  centralHi := (87040956880586554267/20000000000000000000)
  directionLo := (109514654211516211637/25000000000000000000)
  directionHi := (438058616846064846549/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree078.table
  base := (7734847627010203430605463274515670137763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3734173056513056731424446960356891834500000000000)
      constant := (77914996087179854358130462140988960234671200383107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree078.table
  base := (15469695245595307095878225573148233845207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7470321032029066363815088490864691919000000000000)
      constant := (155911394751250432024686613221127631611684092519223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109514654211516211637/25000000000000000000)
  centralHi := (438058616846064846549/100000000000000000000)
  directionLo := (440893977299499636451/100000000000000000000)
  directionHi := (110223494324874909113/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree079.table
  base := (16694925097390897164933405746543503374711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7564006125634272619238625066592623124000000000000)
      constant := (159950878314740052196800675134802307625404883182679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree079.table
  base := (16694925090659814890001706135474360047173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7566006364111622352268488797899312249000000000000)
      constant := (160034380545710079458132597301033849902351471274597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440893977299499636451/100000000000000000000)
  centralHi := (110223494324874909113/25000000000000000000)
  directionLo := (88742243975427160327/20000000000000000000)
  directionHi := (110927804969283950409/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree080.table
  base := (8976230157201774422477552923016048362743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3829833069121215887814178106235731289500000000000)
      constant := (82063150908326095569746443184947535569543926218327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree080.table
  base := (8976230154513366556473389320740253142437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3830845848097089170360944552466966289500000000000)
      constant := (82105965218311457048372674346531613694723815434693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88742243975427160327/20000000000000000000)
  centralHi := (110927804969283950409/25000000000000000000)
  directionLo := (223255343760647869227/50000000000000000000)
  directionHi := (89302137504259147691/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree081.table
  base := (19242300890705954728030194862615786005269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7755326150850590932018087358350302034000000000000)
      constant := (168356262678301220837331499767847095614371042447541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree081.table
  base := (9621150443205801840311997616587379200171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3878688514138367164587644705984276454500000000000)
      constant := (84222022211101264455943361008901575361122613972619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223255343760647869227/50000000000000000000)
  centralHi := (89302137504259147691/20000000000000000000)
  directionLo := (449292712490002956269/100000000000000000000)
  directionHi := (44929271249000295627/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree082.table
  base := (2056444681498280900771362821816522451441/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3925493081729375044203909252114570744500000000000)
      constant := (86320380449136027464141882573567652188546193868245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree082.table
  base := (10282223405776761388230713037106074424449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-3926531180179645158814344859501586619500000000000)
      constant := (86365361250520320513289040999088232315942561046561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449292712490002956269/100000000000000000000)
  centralHi := (44929271249000295627/10000000000000000000)
  directionLo := (452057616817268892519/100000000000000000000)
  directionHi := (11301440420431722313/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree083.table
  base := (21918898078314331600314983151069687852987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-7946646176066909244797549650107980944000000000000)
      constant := (176979796475449190273090981002998691416877811343643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree083.table
  base := (1369931129723516039599574360486878212887/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-993593461555230788260261253254724196125000000000)
      constant := (22133995584003399147711329546895553306111512869486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452057616817268892519/100000000000000000000)
  centralHi := (11301440420431722313/2500000000000000000)
  directionLo := (113701428187048557519/25000000000000000000)
  directionHi := (454805712748194230077/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree084.table
  base := (23305654673670178542814081013810237362277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-8042306188675068401187280795986820399000000000000)
      constant := (181373369408953415648243608897089827147245069496453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree084.table
  base := (45518856780242794469626610650233177821/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1005554128065550286816936291634051737375000000000)
      constant := (22683471366785916551475843039743706339432485182016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113701428187048557519/25000000000000000000)
  centralHi := (454805712748194230077/100000000000000000000)
  directionLo := (228768651575274412739/50000000000000000000)
  directionHi := (457537303150548825479/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree085.table
  base := (772647393609694660367317198989409686103/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1017245775160403444697126492733207481750000000000)
      constant := (23227684962261485798696128057461484103175110075468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree085.table
  base := (24724716593765448280121357962279906498487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-8140118356606958282988890640107034229000000000000)
      constant := (185918141287131701186852036175714151159168563493143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228768651575274412739/50000000000000000000)
  centralHi := (457537303150548825479/100000000000000000000)
  directionLo := (14382896309511435963/3125000000000000000)
  directionHi := (460252681904365950817/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree086.table
  base := (6544020959867420380254506968930205333837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2058406553472846678491685771936124827250000000000)
      constant := (47581031835579685652151389652440598495464729629293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree086.table
  base := (5235216767615434657736348587701155590957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-8235803688689514271442290947141654559000000000000)
      constant := (190423075730017229191097980004724649867322877204865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14382896309511435963/3125000000000000000)
  centralHi := (460252681904365950817/100000000000000000000)
  directionLo := (231476067135484722301/50000000000000000000)
  directionHi := (462952134270969444603/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree087.table
  base := (27659756402110653928797480751950580767173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-8329286226499545870356474233623338764000000000000)
      constant := (194881312341204044566477864259086333113089633354597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree087.table
  base := (1728734775062465278922685787030338673831/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1041436127596508782486961406772034361125000000000)
      constant := (24372821782814525975410617279932927968998735064718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231476067135484722301/50000000000000000000)
  centralHi := (462952134270969444603/100000000000000000000)
  directionLo := (232817968621372722163/50000000000000000000)
  directionHi := (465635937242745444327/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree088.table
  base := (7293933570181561948667997623661138291549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2106236559776926256686551344875544554750000000000)
      constant := (49873258673602317228111228934681328213774450958461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree088.table
  base := (5835146855967925890475181883023146571737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-8427174352854626248349091561210895219000000000000)
      constant := (199596636884291897797658400187491306764167655311965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232817968621372722163/50000000000000000000)
  centralHi := (465635937242745444327/100000000000000000000)
  directionLo := (234152179937436321573/50000000000000000000)
  directionHi := (468304359874872643147/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree089.table
  base := (15362008736592997324086151865563212693/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1065075781464483022891992065672627209250000000000)
      constant := (25519911800208497543532402078960113365423567219250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree089.table
  base := (3840502184059833217833115054961559679149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1065357460617147779600311483530689443625000000000)
      constant := (25533157949384911287368933185152589036367377894861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234152179937436321573/50000000000000000000)
  centralHi := (468304359874872643147/100000000000000000000)
  directionLo := (470957663600135589777/100000000000000000000)
  directionHi := (235478831800067794889/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree090.table
  base := (8076151494453486927014294840608850433417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2154066566081005834881416917814964282250000000000)
      constant := (52220022865692646456466885635097819944393058543913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree090.table
  base := (16152302988624862040013572782768993968281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4309272508509869112627946087640067939500000000000)
      constant := (104494227197334966246229154513761201523842304068409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470957663600135589777/100000000000000000000)
  centralHi := (235478831800067794889/50000000000000000000)
  directionLo := (94719220505572728583/20000000000000000000)
  directionHi := (118399025631965910729/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree091.table
  base := (4239687474161565567926752760819104627719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1088990784616522811989424852142337073000000000000)
      constant := (26706928234694038644968073311590272372754292125591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree091.table
  base := (16958749896421254501048579498472166775179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4357115174551147106854646241157378104500000000000)
      constant := (106883104641449979748608245972558863406501663623531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94719220505572728583/20000000000000000000)
  centralHi := (118399025631965910729/25000000000000000000)
  directionLo := (476219923727963091399/100000000000000000000)
  directionHi := (2381099618639815457/500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree092.table
  base := (35562698918586662792239979300362209790383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-8807586289540341652305129963017536039000000000000)
      constant := (218485297645883705979815138725585532555546095094287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree092.table
  base := (889067472955694527419149662908916176753/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1101239460148106275270336598668672067375000000000)
      constant := (27324816032455081894786125688255637133105319296085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476219923727963091399/100000000000000000000)
  centralHi := (2381099618639815457/500000000000000000)
  directionLo := (59853670937617628087/12500000000000000000)
  directionHi := (478829367500941024697/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree093.table
  base := (4655025419110499903247686756862570699727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1112905787768562601086857638612046936750000000000)
      constant := (27921213345957897819479237649726454291961574809503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree093.table
  base := (37240203352597829432609094818779003657379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-8905601013267406190616093096383996869000000000000)
      constant := (223485411324791007559332183533118242295820948819331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59853670937617628087/12500000000000000000)
  centralHi := (478829367500941024697/100000000000000000000)
  directionLo := (481424667634756216117/100000000000000000000)
  directionHi := (240712333817378108059/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree094.table
  base := (7790002619109537654486184577135769626709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-8998906314756659965084592254775214949000000000000)
      constant := (228308653242811095305968673415837293294189741458505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree094.table
  base := (38950013095319524832515095171054376505687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9001286345349962179069493403418617199000000000000)
      constant := (228426858478271837888985485255288187376764821813943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481424667634756216117/100000000000000000000)
  centralHi := (240712333817378108059/50000000000000000000)
  directionLo := (242003025824637026333/50000000000000000000)
  directionHi := (484006051649274052667/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree095.table
  base := (40692128146079190662756421389004407469903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9094566327364819121474323400654054404000000000000)
      constant := (233302137071265097164012911291609196918027602059567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree095.table
  base := (20346064072948648164872915741993583341263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4548485838716259083761446855226618764500000000000)
      constant := (116711434860010585147692700437618946142062263394607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242003025824637026333/50000000000000000000)
  centralHi := (484006051649274052667/100000000000000000000)
  directionLo := (60821717628631118871/12500000000000000000)
  directionHi := (486573741029048950969/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree096.table
  base := (42466548504088926538911952923890304706039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9190226339972978277864054546532893859000000000000)
      constant := (238350158252976467471994684944330242172591532554071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree096.table
  base := (42466548503943934499790040516893011237953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9192657009515074155976294017487857859000000000000)
      constant := (238473445049990580565766567737342886577089659586017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60821717628631118871/12500000000000000000)
  centralHi := (486573741029048950969/100000000000000000000)
  directionLo := (489127951445108324903/100000000000000000000)
  directionHi := (61140993930638540613/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree097.table
  base := (44273274169273132004873036454484382201323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9285886352581137434253785692411733314000000000000)
      constant := (243452716787907217672300523644166567543796899503947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree097.table
  base := (22136637084578784074980067943630993167801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4644171170798815072214847162261239094500000000000)
      constant := (121789292234071158421513827875981560321627684313689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489127951445108324903/100000000000000000000)
  centralHi := (61140993930638540613/12500000000000000000)
  directionLo := (491668892966366644469/100000000000000000000)
  directionHi := (49166889296636664447/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree098.table
  base := (23056152570697804430710741792105236794737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4690773182594648295321758419145286384500000000000)
      constant := (124304906338013904469416740275368314158148807109393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree098.table
  base := (23056152570651755057025788791903035253709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4692013836840093066441547315778549259500000000000)
      constant := (124369143987223514635044133537903430143002832894701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491668892966366644469/100000000000000000000)
  centralHi := (49166889296636664447/10000000000000000000)
  directionLo := (247098385130628055371/50000000000000000000)
  directionHi := (494196770261256110743/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree099.table
  base := (23991820710136666977557411464397732254863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4738603188898727873516623992084706112000000000000)
      constant := (126910722958657676244774435800913053085848859545007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree099.table
  base := (47983641420199943394677890399234218830253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9479713005762742121336494938591718849000000000000)
      constant := (253952555568881979906163734783939118352975617920717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247098385130628055371/50000000000000000000)
  centralHi := (494196770261256110743/100000000000000000000)
  directionLo := (496711782790121664721/100000000000000000000)
  directionHi := (248355891395060832361/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree100.table
  base := (49887283005765112836932913671303117496023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9572866390405614903422979130048251679000000000000)
      constant := (259087616511752190618802601436160912706909595912247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree100.table
  base := (24943641502853318101096529504008408845669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4787699168922649054894947622813169589500000000000)
      constant := (129610693625714815717649686354431496355692445003141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496711782790121664721/100000000000000000000)
  centralHi := (248355891395060832361/50000000000000000000)
  directionLo := (7800220702951440213/1562500000000000000)
  directionHi := (499214124988892173633/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree101.table
  base := (25911614948881317300949715032500635572221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4834263201506887029906355137963545567000000000000)
      constant := (132204162229662389010082601599378590198446555855069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree101.table
  base := (51823229897716045846616850309663366267819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9671083669927854098243295552660959509000000000000)
      constant := (264544783022076534623640567478930255678973281284491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7800220702951440213/1562500000000000000)
  centralHi := (499214124988892173633/100000000000000000000)
  directionLo := (100340797288901289641/20000000000000000000)
  directionHi := (250851993222253224103/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree102.table
  base := (53791482096183420599721755987063644955911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9764186415621933216202441421805930589000000000000)
      constant := (269783569760022799955777672616821093366663657189479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree102.table
  base := (13447870524036576660517969050842139111577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2441692250502602521674173964923894959750000000000)
      constant := (67480685720203112847586214605399878733648233604153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100340797288901289641/20000000000000000000)
  centralHi := (250851993222253224103/50000000000000000000)
  directionLo := (504181552062542013141/100000000000000000000)
  directionHi := (252090776031271006571/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree103.table
  base := (55792039600965266845217795057619033799517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9859846428230092372592172567684770044000000000000)
      constant := (275213352413838477227039373145137208816735074466813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree103.table
  base := (27896019800467851814376780814018128371719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4931227167046483037575048083365100084500000000000)
      constant := (137677633413814831847037714919933972247528580191591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504181552062542013141/100000000000000000000)
  centralHi := (252090776031271006571/50000000000000000000)
  directionLo := (253323501113733038051/50000000000000000000)
  directionHi := (506647002227466076103/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree104.table
  base := (28912451206030932235999048173386629740583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-4977753220419125764490951856781804749500000000000)
      constant := (140348836210383009235391735387711192999039512542087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree104.table
  base := (57824902412038318037123961810240047794199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-9958139666175522063603496473764820499000000000000)
      constant := (280842354862522428956978357594260615575478104104311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253323501113733038051/50000000000000000000)
  centralHi := (506647002227466076103/100000000000000000000)
  directionLo := (509100512955901732367/100000000000000000000)
  directionHi := (31818782059743858273/6250000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree105.table
  base := (59890070529439349240789122538313507141909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10051166453446410685371634859442448954000000000000)
      constant := (286236529780801188642551043199688618869183740024501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree105.table
  base := (1497251763235514919265440855697768857647/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1256728124782259756507112097599930103625000000000)
      constant := (35798000873185818880742849973488585736387237811915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509100512955901732367/100000000000000000000)
  centralHi := (31818782059743858273/6250000000000000000)
  directionLo := (63942782005409741779/12500000000000000000)
  directionHi := (511542256043277934233/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree106.table
  base := (61987543953073583703421626509937772413177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32256054929700017715882287515560000000000000)
      linear := (-3612255772892335294325868994418401000000000000)
      constant := (103891037555692762237596397432291241815607053217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree106.table
  base := (61987543953058650519548924683345817908091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32256054929700017715882287515560000000000000)
      linear := (-3613211224756366692954893943693151000000000000)
      constant := (103944543679786059941654291832045841409086119411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63942782005409741779/12500000000000000000)
  centralHi := (511542256043277934233/100000000000000000000)
  directionLo := (513972399204208992707/100000000000000000000)
  directionHi := (128493099801052248177/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree107.table
  base := (64117322682948017107630141085228765086251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10242486478662728998151097151200127864000000000000)
      constant := (297477856560183290090734297420845805006381340985739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree107.table
  base := (16029330670734031600085346013399061190659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2561298915605797507240924348717170372250000000000)
      constant := (74407750873904464466051732069858591028521046113251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513972399204208992707/100000000000000000000)
  centralHi := (128493099801052248177/25000000000000000000)
  directionLo := (516391106206928224409/100000000000000000000)
  directionHi := (51639110620692822441/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree108.table
  base := (13255881343810400170292509186474132734039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10338146491270888154540828297078967319000000000000)
      constant := (303180325979526819829810397729144342030435451230355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree108.table
  base := (66279406719042533575653490457046226328441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10340880994505746017417097701903301819000000000000)
      constant := (303336347882781685531485754512564281168513177626649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516391106206928224409/100000000000000000000)
  centralHi := (51639110620692822441/10000000000000000000)
  directionLo := (259399268501040340707/50000000000000000000)
  directionHi := (103759707400416136283/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree109.table
  base := (68473796061379463109158402361891058406161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10433806503879047310930559442957806774000000000000)
      constant := (308937332751970799003209683813280460088162399111729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree109.table
  base := (68473796061371925994263802260582294182223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10436566326588302005870498008937922149000000000000)
      constant := (309096256358009781767816063139126023841376481264047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259399268501040340707/50000000000000000000)
  centralHi := (103759707400416136283/20000000000000000000)
  directionLo := (521194847846161589933/100000000000000000000)
  directionHi := (260597423923080794967/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree110.table
  base := (70700490709927866612083531574970192977273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10529466516487206467320290588836646229000000000000)
      constant := (314748876877514910301413309544739126651469149993497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree110.table
  base := (70700490709921866647502418304883946658931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10532251658670857994323898315972542479000000000000)
      constant := (314910728921301841802138907750454462607219168146259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521194847846161589933/100000000000000000000)
  centralHi := (260597423923080794967/50000000000000000000)
  directionLo := (52358019141987006907/10000000000000000000)
  directionHi := (523580191419870069071/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree111.table
  base := (2279984083271793425932336584763787033057/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1328140816136920702963752716839435710500000000000)
      constant := (40076869794519897002340744951546144056372456861492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree111.table
  base := (36479745332346306858761643609003665619699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-5313968495376706991388649311503581404500000000000)
      constant := (160389882786328948961291265040653275166651425273811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52358019141987006907/10000000000000000000)
  centralHi := (523580191419870069071/100000000000000000000)
  directionLo := (10519094338832636131/2000000000000000000)
  directionHi := (525954716941631806551/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree112.table
  base := (75250795925690282866011855438489517187657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10720786541703524780099752880594325139000000000000)
      constant := (326535577187903877626989707418868649534345101527273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree112.table
  base := (15050159185137296319142497464547254085559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10723622322835969971230698930041783139000000000000)
      constant := (326703366312078239565751019088443608919465854096755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10519094338832636131/2000000000000000000)
  centralHi := (525954716941631806551/100000000000000000000)
  directionLo := (264159285138264772789/50000000000000000000)
  directionHi := (528318570276529545579/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree113.table
  base := (2424200202903448905522109866587740472089/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1352055819288960492061185503309145574250000000000)
      constant := (41563841671593686585673022063982853008568620160084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree113.table
  base := (19393601623226834922502879567569811523701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2704826913729631489921024809269100867250000000000)
      constant := (83170382784890837659456067815034862335230358448789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264159285138264772789/50000000000000000000)
  centralHi := (528318570276529545579/100000000000000000000)
  directionLo := (66333986755108300593/12500000000000000000)
  directionHi := (106134378808173280949/20000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree114.table
  base := (79930322366362627302550246690329346637037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-10912106566919843092879215172352004049000000000000)
      constant := (338540426910696645408417791427513438971881715694093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree114.table
  base := (1998258059159005494507448235337985756071/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1364374123375135243517187443013877974875000000000)
      constant := (42339282506889232551327816675129740220623839538595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66333986755108300593/12500000000000000000)
  centralHi := (106134378808173280949/20000000000000000000)
  directionLo := (533014827702574136737/100000000000000000000)
  directionHi := (266507413851287068369/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree115.table
  base := (82318543546052924622887157268324472316297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11007766579528002249268946318230843504000000000000)
      constant := (344624657801746067991803909364893646412664499192233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree115.table
  base := (20579635886512752216204293094846157816807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2752669579770909484147724962786411032250000000000)
      constant := (86200388264682626277284531397044209137370739031623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533014827702574136737/100000000000000000000)
  centralHi := (266507413851287068369/50000000000000000000)
  directionLo := (535347507677666363451/100000000000000000000)
  directionHi := (133836876919416590863/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree116.table
  base := (21184767507996933411258508554568504060599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2775856648034040351414669366027420739750000000000)
      constant := (87690856511474642602312461294256685557750435973911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree116.table
  base := (84739070031986209317910479593714727805827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11106363651166193925044300158180264459000000000000)
      constant := (350943410150414097916983449060361959312670815842403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535347507677666363451/100000000000000000000)
  centralHi := (133836876919416590863/25000000000000000000)
  directionLo := (268835033711462771163/50000000000000000000)
  directionHi := (537670067422925542327/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree117.table
  base := (87191901824173964809815125598506275624837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11199086604744320562048408609988522414000000000000)
      constant := (356956731643155016876953844064896505470154020928293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree117.table
  base := (87191901824172752025937223935555874585217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11202048983248749913497700465214884789000000000000)
      constant := (357139831330165505607264924060207260972075324974113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268835033711462771163/50000000000000000000)
  centralHi := (537670067422925542327/100000000000000000000)
  directionLo := (269991318762500931967/50000000000000000000)
  directionHi := (107996527505000372787/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree118.table
  base := (44838519461309408022832335188404125852301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-5647373308676239859219069877933680934500000000000)
      constant := (181602287296758153782083875261959132983080452534189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree118.table
  base := (350300933291475981258017853077654891127/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1412216789416413237743887596531188139875000000000)
      constant := (45423852074748203798224159074774232636179934131296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269991318762500931967/50000000000000000000)
  centralHi := (107996527505000372787/20000000000000000000)
  directionLo := (108457069157218480257/20000000000000000000)
  directionHi := (271142672893046200643/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree119.table
  base := (18438896265465931901992330740527215581793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11390406629960638874827870901746201324000000000000)
      constant := (369506954896983364429126208016221596393353101418885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree119.table
  base := (23048620331832222993273508340129253604391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2848354911853465472601125269821031362250000000000)
      constant := (92424091488468848958189248603111338836529046616199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108457069157218480257/20000000000000000000)
  centralHi := (271142672893046200643/50000000000000000000)
  directionLo := (272289158653179789181/50000000000000000000)
  directionHi := (544578317306359578363/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree120.table
  base := (4737211451915697712708388931936855330359/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2871516660642199507804400511906260194750000000000)
      constant := (93965968138389280074248360457475853893783113632755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree120.table
  base := (47372114519156671859351927903608971691009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-5744552489748208939428950693159372889500000000000)
      constant := (188028239698917868032478647704785783557993051434401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272289158653179789181/50000000000000000000)
  centralHi := (544578317306359578363/100000000000000000000)
  directionLo := (109372334912647870897/20000000000000000000)
  directionHi := (273430837281619677243/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree121.table
  base := (760361578559212337860427561224291159059/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1447715831897119648450916649187985029250000000000)
      constant := (47784415945404813810458403853145340717603523923616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree121.table
  base := (97326282055578693630807407337517464560827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11584790311578973867311301693353366109000000000000)
      constant := (382471156929867587426790407239077076220552634037403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109372334912647870897/20000000000000000000)
  centralHi := (273430837281619677243/50000000000000000000)
  directionLo := (109827107497556278199/20000000000000000000)
  directionHi := (137283884371945347749/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree122.table
  base := (99940640379132782363359328715717432121331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11677386667785116343997064339382719689000000000000)
      constant := (388741319926028466416901462838161474208735840859859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree122.table
  base := (99940640379132396134952979622787729817529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11680475643661529855764702000387986439000000000000)
      constant := (388940398549971882164906187802206639900700239982681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109827107497556278199/20000000000000000000)
  centralHi := (137283884371945347749/25000000000000000000)
  directionLo := (27570001176907791981/5000000000000000000)
  directionHi := (551400023538155839621/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree123.table
  base := (25646826002245535475455634473094523936447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-2943261670098318875096698871315389786000000000000)
      constant := (98815462410481977705655301764276222277338767795583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree123.table
  base := (102587304008981834740266445936546172276287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11776160975744085844218102307422606769000000000000)
      constant := (395464204258149543657182945647225105575528419037343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27570001176907791981/5000000000000000000)
  centralHi := (551400023538155839621/100000000000000000000)
  directionLo := (69206905971306779081/12500000000000000000)
  directionHi := (553655247770454232649/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree124.table
  base := (105266272945134537879065768017262029252859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11868706693001434656776526631140398599000000000000)
      constant := (401836916710937754136100103584411486499715598329051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree124.table
  base := (52633136472567146807157611050611596941201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-5935923153913320916335751307228613549500000000000)
      constant := (201021287027200741428947226084968067025190560106289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69206905971306779081/12500000000000000000)
  centralHi := (553655247770454232649/100000000000000000000)
  directionLo := (555901322906905231557/100000000000000000000)
  directionHi := (277950661453452615779/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree125.table
  base := (21595509437519426197783774160099553898801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11964366705609593813166257777019238054000000000000)
      constant := (408466521133058891870049399127895717322778803863445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree125.table
  base := (107977547187596936754364495516114284188997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-11967531639909197821124902921491847429000000000000)
      constant := (408675507938728595692877889103984858208776744242533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555901322906905231557/100000000000000000000)
  centralHi := (277950661453452615779/50000000000000000000)
  directionLo := (139534589850404918267/25000000000000000000)
  directionHi := (558138359401619673069/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree126.table
  base := (110721126736376947521599112853731631046859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12060026718217752969555988922898077509000000000000)
      constant := (415150662908292202728733230748986831128356721595051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree126.table
  base := (2768028168409419826999087469915751623549/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1507902121498969226197287903565808469875000000000)
      constant := (51920375738891470149402538198824582991428541532305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139534589850404918267/25000000000000000000)
  centralHi := (558138359401619673069/100000000000000000000)
  directionLo := (140091616375993353077/25000000000000000000)
  directionHi := (560366465503973412309/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree127.table
  base := (113497011591480868922623382559645181523207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12155686730825912125945720068776916964000000000000)
      constant := (421889342036638547302211521849693021211698259061223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree127.table
  base := (3546781612233773316539021539463034111509/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1519862788009288724753962941945136011125000000000)
      constant := (52763133496451480027085444874310860362030788235604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140091616375993353077/25000000000000000000)
  centralHi := (560366465503973412309/100000000000000000000)
  directionLo := (562585747319730876281/100000000000000000000)
  directionHi := (281292873659865438141/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree128.table
  base := (116305201752915624947525750837602061701581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12251346743434071282335451214655756419000000000000)
      constant := (428682558518098767210272458261279664693746190352109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree128.table
  base := (116305201752915527323086823724839974653829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12254587636156865786485103842595708419000000000000)
      constant := (428901694120169674585321489859421971308980806633381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562585747319730876281/100000000000000000000)
  centralHi := (281292873659865438141/50000000000000000000)
  directionLo := (112959261774001396741/20000000000000000000)
  directionHi := (282398154435003491853/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree129.table
  base := (119145697220687789592847888425481568725623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12347006756042230438725182360534595874000000000000)
      constant := (435530312352673684593564229093432199418963543586647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree129.table
  base := (59572848610343855991604848028300777719869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6175136484119710887469252074815164374500000000000)
      constant := (217876442178403043303754943461162774465449402286941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112959261774001396741/20000000000000000000)
  centralHi := (282398154435003491853/50000000000000000000)
  directionLo := (70874781518520017189/12500000000000000000)
  directionHi := (566998252148160137513/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree130.table
  base := (122018497994803779159968929984135152934643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12442666768650389595114913506413435329000000000000)
      constant := (442432603540364101871458578922098896071693303977427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree130.table
  base := (61009248997401858732718881202393466509479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6222979150160988881695952228332474539500000000000)
      constant := (221329319340760939417244193802324481649239057396231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70874781518520017189/12500000000000000000)
  centralHi := (566998252148160137513/100000000000000000000)
  directionLo := (284595838587352166929/50000000000000000000)
  directionHi := (569191677174704333859/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree131.table
  base := (15615450509408731493385018379180004146433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1567290847657318593938080581536534348000000000000)
      constant := (56173679010146350212941164723476981622895010902737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree131.table
  base := (62461802037634901453454383174827465187687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6270821816202266875922652381849784704500000000000)
      constant := (224809478547158917015374509520576206650912425311943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284595838587352166929/50000000000000000000)
  centralHi := (569191677174704333859/100000000000000000000)
  directionLo := (114275336410064807499/20000000000000000000)
  directionHi := (71422085256290504687/12500000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree132.table
  base := (127861015462092109173888432090513864112723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12633986793866707907894375798171114239000000000000)
      constant := (456400797975094547105195266398551727800102576778547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree132.table
  base := (15982626932761508774346587752490107151833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1579666120560886217537338133841773717375000000000)
      constant := (57079229949399339411897586895490754474900980393337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114275336410064807499/20000000000000000000)
  centralHi := (71422085256290504687/12500000000000000000)
  directionLo := (573553363007071330443/100000000000000000000)
  directionHi := (143388340751767832611/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree133.table
  base := (65415366077638248414841159624851967440599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6364823403237433532142053472024976847000000000000)
      constant := (231733350611068040839419224150852335144375323793911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree133.table
  base := (65415366077638232924639748859279575357413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6366507148284822864376052688884405034500000000000)
      constant := (231851643092076633148283600079413225542085062141957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573553363007071330443/100000000000000000000)
  centralHi := (143388340751767832611/25000000000000000000)
  directionLo := (35982613403613808313/6250000000000000000)
  directionHi := (575721814457820933009/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree134.table
  base := (26766550830965761640625958250438283690279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12825306819083026220673838089928793149000000000000)
      constant := (470587141822296129930179310909547617197716630037155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree134.table
  base := (133832754154828783581455273282434603198933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-12828699628652201717205505684803430399000000000000)
      constant := (470827296861194211593448874238304733446726326325237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35982613403613808313/6250000000000000000)
  centralHi := (575721814457820933009/100000000000000000000)
  directionLo := (144470532261013752049/25000000000000000000)
  directionHi := (577882129044055008197/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree135.table
  base := (3421677036518867172636867877220954727163/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1615120853961398172132946154475954075500000000000)
      constant := (59720264971946924705794515860292715273992414748535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree135.table
  base := (68433540730377333669244579611592439318171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6462192480367378852829452995919025364500000000000)
      constant := (239002935813159128507488566525250298848018973674619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144470532261013752049/25000000000000000000)
  centralHi := (577882129044055008197/100000000000000000000)
  directionLo := (580034397682046178693/100000000000000000000)
  directionHi := (290017198841023089347/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree136.table
  base := (279867428146119260481431084447530191471/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-3254156711074836133363325095421618014750000000000)
      constant := (121247908770493643079349455054245310118804427289875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree136.table
  base := (69966857036529807345786715092099703910197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6510035146408656847056153149436335529500000000000)
      constant := (242619505239763045042298011791531991637560538709333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580034397682046178693/100000000000000000000)
  centralHi := (290017198841023089347/50000000000000000000)
  directionLo := (116435741921500779349/20000000000000000000)
  directionHi := (291089354803751948373/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree137.table
  base := (28606530398349798561859385249590509480759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13112286856907503689843031527565311514000000000000)
      constant := (492275687741494323586899798464336197006785629360755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree137.table
  base := (71516325995874490226825414149963401426519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6557877812449934841282853302953645694500000000000)
      constant := (246263356710409190236237927876793901455102337188791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116435741921500779349/20000000000000000000)
  centralHi := (291089354803751948373/50000000000000000000)
  directionLo := (584315152418746199487/100000000000000000000)
  directionHi := (9129924256542909367/1562500000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree138.table
  base := (146163895216827990257723525499163422773221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13207946869515662846232762673444150969000000000000)
      constant := (499614277754135303720948738832246806797759981144069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree138.table
  base := (3654097380420699511005340300652691625949/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1651430119622803208877388364117738964875000000000)
      constant := (62483622556274472558229601211000363164610055400305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584315152418746199487/100000000000000000000)
  centralHi := (9129924256542909367/1562500000000000000)
  directionLo := (58644381211845594437/10000000000000000000)
  directionHi := (586443812118455944371/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree139.table
  base := (149327443748301703106814859795618905341667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13303606882123822002622493819322990424000000000000)
      constant := (507007405119898148086882184330405183945361995428163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree139.table
  base := (149327443748301695306458724469021405132861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13307126289064981659472507219976532049000000000000)
      constant := (507265811567658925448821600285542666295727573768029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58644381211845594437/10000000000000000000)
  centralHi := (586443812118455944371/100000000000000000000)
  directionLo := (73570596644259730091/12500000000000000000)
  directionHi := (588564773154077840729/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree140.table
  base := (3813082439654377015181074962722190158759/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1674908361841497644876528120650228734875000000000)
      constant := (64306883729847934454432514607624031262482397070755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree140.table
  base := (30504659517235014881981418986408690030761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13402811621147537647925907527011152379000000000000)
      constant := (514717206773208434385552673271692342724531824705645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73570596644259730091/12500000000000000000)
  centralHi := (588564773154077840729/100000000000000000000)
  directionLo := (18458691201778436397/3125000000000000000)
  directionHi := (118135623691381992941/20000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree141.table
  base := (9734466045653309036466456578816876078011/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1686865863417517539425244513885083666750000000000)
      constant := (65244658988848986172698121487737135228562103342758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree141.table
  base := (38937864182613234914992129263968400523713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-3374624238307523409094826958511443177250000000000)
      constant := (130555791516711227575389205432688325360767880162657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18458691201778436397/3125000000000000000)
  centralHi := (118135623691381992941/20000000000000000000)
  directionLo := (1481959823699852391/250000000000000000)
  directionHi := (592783929479940956401/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree142.table
  base := (79505960590569996618448722000781770337901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6795293459974149735895843628479754394500000000000)
      constant := (264757005667961988439962880910080520081723256392589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree142.table
  base := (159011921181139989325606847217445059080609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13594182285312649624832708141080393039000000000000)
      constant := (529783689448568940759949850100694199595945771348801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1481959823699852391/250000000000000000)
  centralHi := (592783929479940956401/100000000000000000000)
  directionLo := (118976457246896348397/20000000000000000000)
  directionHi := (297441143117240870993/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree143.table
  base := (162304690938240804886836781508746224427649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13686246932556458628181418402838348244000000000000)
      constant := (537125288114180310692753543787199660010694851411361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree143.table
  base := (162304690938240801779808926604425003044717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13689867617395205613286108448115013369000000000000)
      constant := (537398776918381098329717944144168848057845752169613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118976457246896348397/20000000000000000000)
  centralHi := (297441143117240870993/50000000000000000000)
  directionLo := (29848663366281919577/5000000000000000000)
  directionHi := (596973267325638391541/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree144.table
  base := (20703720750219980204182491878963208622029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1722738368145577223071393693589648462375000000000)
      constant := (68098887780695181106004565310613802800196340883181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree144.table
  base := (8281488300087991958271912461382032617541/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-3446388237369440400434877188787408424750000000000)
      constant := (136267107119070485261041864354731464806155049482745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29848663366281919577/5000000000000000000)
  centralHi := (596973267325638391541/100000000000000000000)
  directionLo := (599056949986670608359/100000000000000000000)
  directionHi := (14976423749666765209/2500000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree145.table
  base := (168987146371701452931960479863340401691041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13877566957772776940960880694596027154000000000000)
      constant := (552511453730067935286418634835506242497755073338049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree145.table
  base := (168987146371701450971618448214531381891037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-13881238281560317590192909062184254029000000000000)
      constant := (552792644122272012848185602541706273198756940900093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599056949986670608359/100000000000000000000)
  centralHi := (14976423749666765209/2500000000000000000)
  directionLo := (150283352528069585077/25000000000000000000)
  directionHi := (601133410112278340309/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree146.table
  base := (86188416024034939535171708003239194559939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-6986613485190468048675305920237433304500000000000)
      constant := (280143171283850150148075499484392892175312551211171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree146.table
  base := (538677600150218367229136969280850413057/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1747115451705359197330788671152359294875000000000)
      constant := (70071427982043980504174533168079071125100143914920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150283352528069585077/25000000000000000000)
  centralHi := (601133410112278340309/100000000000000000000)
  directionLo := (120640544458171420463/20000000000000000000)
  directionHi := (150800680572714275579/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree147.table
  base := (4394970575771731363654884697556568396823/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1758610872873636906717542873294213258000000000000)
      constant := (71014471094807382616923634046472886899825386767235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree147.table
  base := (175798823030869253309576358866846314375533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14072608945725429567099709676253494689000000000000)
      constant := (568404767678521951660635593396955575934087511082637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120640544458171420463/20000000000000000000)
  centralHi := (150800680572714275579/25000000000000000000)
  directionLo := (605264959835760794983/100000000000000000000)
  directionHi := (75658119979470099373/12500000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree148.table
  base := (179253119320103611339839903002230210822761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14164546995597254410130074132232545519000000000000)
      constant := (575999732302344721441531770941075055621606760229129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree148.table
  base := (7170124772804144414309418336329974731351/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14168294277807985555553109983288115019000000000000)
      constant := (576292675588782839969433005626305175171641708490975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605264959835760794983/100000000000000000000)
  centralHi := (75658119979470099373/12500000000000000000)
  directionLo := (75915024351951136527/12500000000000000000)
  directionHi := (607320194815609092217/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree149.table
  base := (7309588836631075283315741521091056341259/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14260207008205413566519805278111384974000000000000)
      constant := (583938233199357773627479489005306164297920253916275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree149.table
  base := (22842465114472110162869550022735256588149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1782997451236317693000813786290341918625000000000)
      constant := (73029393448391875096797754824762006305385297395861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75915024351951136527/12500000000000000000)
  centralHi := (607320194815609092217/100000000000000000000)
  directionLo := (609368498083674845181/100000000000000000000)
  directionHi := (304684249041837422591/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree150.table
  base := (23282328477236612890306437341549359147791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1794483377601696590363692052998778053625000000000)
      constant := (73991408931187337158104947453818221632675217938799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree150.table
  base := (4656465695447322562577329961571149923587/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1794958117746637191557488824669669459875000000000)
      constant := (74029022959197364231054442059271389616524646335215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609368498083674845181/100000000000000000000)
  centralHi := (304684249041837422591/50000000000000000000)
  directionLo := (611409939306385406129/100000000000000000000)
  directionHi := (61140993930638540613/10000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree151.table
  base := (94904920013227708741018399112649026094877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-7225763516710865939649633784934531942000000000000)
      constant := (299989423526383980227110572907892351272319858137853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree151.table
  base := (189809840026455416990218116228745799316017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14455350274055653520913310904391976009000000000000)
      constant := (600283783848115047293271767073583224148607635535313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611409939306385406129/100000000000000000000)
  centralHi := (61140993930638540613/10000000000000000000)
  directionLo := (613444586990970308791/100000000000000000000)
  directionHi := (76680573373871288599/12500000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree152.table
  base := (96696678770734038860557152357199564932473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-7273593523014945517844499357873951669500000000000)
      constant := (304040480004583009991422203046309725539227392886297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree152.table
  base := (193393357541468077330589131476575428065051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14551035606138209509366711211426596339000000000000)
      constant := (608389948110743857896960491766809681296771536818939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613444586990970308791/100000000000000000000)
  centralHi := (76680573373871288599/12500000000000000000)
  directionLo := (615472508512286348071/100000000000000000000)
  directionHi := (76934063564035793509/12500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree153.table
  base := (197009180362934448695452099061215854457317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14642847058638050192078729861626742794000000000000)
      constant := (616237610318693321669750075356102108023349186331013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree153.table
  base := (384783555396356344502679193697566134647/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1830840117277595687227513939807652083625000000000)
      constant := (77068834557683223934902178037413606711180176984512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615472508512286348071/100000000000000000000)
  centralHi := (76934063564035793509/12500000000000000000)
  directionLo := (308746885069424888181/50000000000000000000)
  directionHi := (617493770138849776363/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree154.table
  base := (12541081780678625638809357097427325417963/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1842313383905776168558557625938197781125000000000)
      constant := (78056099747668787587367045398768172442470578401814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree154.table
  base := (12541081780678625623422110021425083348667/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1842800783787915185784188978186979624875000000000)
      constant := (78095746112535160403072132806372243821014657702326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308746885069424888181/50000000000000000000)
  centralHi := (617493770138849776363/100000000000000000000)
  directionLo := (12390168741162081467/2000000000000000000)
  directionHi := (619508437058104073351/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree155.table
  base := (102168870962621079821889331762221894979561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-7417083541927184252429096076692210852000000000000)
      constant := (316357261498568690970389717703335772405052439104329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree155.table
  base := (204337741925242159448313548516562821494279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14838091602385877474726912132530457329000000000000)
      constant := (633035825427190758003841632481298538206222748163431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12390168741162081467/2000000000000000000)
  centralHi := (619508437058104073351/100000000000000000000)
  directionLo := (621516573400950546933/100000000000000000000)
  directionHi := (310758286700475273467/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree156.table
  base := (52012620166522553579955234874845852231341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-3732456774115631915311980824815815289750000000000)
      constant := (160258696341513745065527681221771098413883515244749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree156.table
  base := (208050480666090214164639587343217162061913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-14933776934468433463180312439565077659000000000000)
      constant := (641360246042194630684181038916195841479993026142457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621516573400950546933/100000000000000000000)
  centralHi := (310758286700475273467/50000000000000000000)
  directionLo := (31175912113278394083/5000000000000000000)
  directionHi := (623518242265567881661/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree157.table
  base := (10589776235670270700323297103635112250243/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-3756371777267671704409413611285525153500000000000)
      constant := (162352396272025875206333458510766585130419836029135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree157.table
  base := (211795524713405413883271260842423732518613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15029462266550989451633712746599697989000000000000)
      constant := (649739230745293306428267759996543228060750424768757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31175912113278394083/5000000000000000000)
  centralHi := (623518242265567881661/100000000000000000000)
  directionLo := (625513505740545664561/100000000000000000000)
  directionHi := (312756752870272832281/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree158.table
  base := (43114574813438184633970295875984981878173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15121147121678845974027385591020940069000000000000)
      constant := (657838922163283339376966914963626136031292878167985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree158.table
  base := (215572874067190923072054201826944329746169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15125147598633545440087113053634318319000000000000)
      constant := (658172779536487180982833527492786320945253394847641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625513505740545664561/100000000000000000000)
  centralHi := (312756752870272832281/50000000000000000000)
  directionLo := (313751212463677941811/50000000000000000000)
  directionHi := (627502424927355883623/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree159.table
  base := (21938252872744983321062222611678540380869/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3205512)
      previous := (1602756)
      next := (1602756)
      square := (16128027464850008857941143757780000000000000)
      linear := (-2708580835579744594235869835688818000000000000)
      constant := (118604983373370395608044657340118103403358343745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree159.table
  base := (219382528727449833132989618269861282992163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6411024)
      previous := (3205512)
      next := (3205512)
      square := (32256054929700017715882287515560000000000000)
      linear := (-5418594848955536286415277095289761000000000000)
      constant := (237330328378702969368826239249349064430094088923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313751212463677941811/50000000000000000000)
  centralHi := (627502424927355883623/100000000000000000000)
  directionLo := (314742529981092704249/50000000000000000000)
  directionHi := (629485059962185408499/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree160.table
  base := (1785795909553481316889912577405291001621/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15312467146895164286806847882778618979000000000000)
      constant := (674861208373038508012410836314964460709877553958625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree160.table
  base := (111612244347092582274807924757241837763863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-7658259131399328708496956833851779489500000000000)
      constant := (337601784691581032045496866651315830350169609446007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314742529981092704249/50000000000000000000)
  centralHi := (629485059962185408499/100000000000000000000)
  directionLo := (631461470037151523887/100000000000000000000)
  directionHi := (39466341877321970243/6250000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree161.table
  base := (45419750793479973801562508825846193382013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15408127159503323443196579028657458434000000000000)
      constant := (683454157507614584966318465498869053367967387856785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree161.table
  base := (56774688491849967239724791071112823442743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-3853050898720303351361828493684544827250000000000)
      constant := (170950202609660954878731681080807952750846660338327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631461470037151523887/100000000000000000000)
  centralHi := (39466341877321970243/6250000000000000000)
  directionLo := (63343171342092169071/10000000000000000000)
  directionHi := (633431713420921690711/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree162.table
  base := (46201064909419366237871753541257620059037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15503787172111482599586310174536297889000000000000)
      constant := (692101643995323474157958001984900003286446585260465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree162.table
  base := (231005324547096831150535312438580855100777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15507888926963769393900714281772799639000000000000)
      constant := (692452615582222267999157102056037413713336215122953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63343171342092169071/10000000000000000000)
  centralHi := (633431713420921690711/100000000000000000000)
  directionLo := (635395847478757856669/100000000000000000000)
  directionHi := (63539584747875785667/10000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree163.table
  base := (11747210021663943551364587042738025099531/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4502141604)
      previous := (2251070802)
      next := (2251070802)
      square := (22651814574381837440978336407802010000000000000)
      linear := (-3899861796179910438994010330103784336000000000000)
      constant := (175200916959041382059751881515968050141731042498295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree163.table
  base := (917750782942495589829992264477215178371/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-1950446782380790672794264323600927496125000000000)
      constant := (87644873101737220274428805609050027451547625597408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635395847478757856669/100000000000000000000)
  centralHi := (63539584747875785667/10000000000000000000)
  directionLo := (318676964346002411793/50000000000000000000)
  directionHi := (637353928692004823587/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree164.table
  base := (119457690812974372668937231385509796087079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-7847553598663900456182886233146988399500000000000)
      constant := (354780114515070545987750077652445632835519299242631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree164.table
  base := (238915381625948745313418894138981490827993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15699259591128881370807514895842040299000000000000)
      constant := (709919918133670646869833471945863058706906991475577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318676964346002411793/50000000000000000000)
  centralHi := (637353928692004823587/100000000000000000000)
  directionLo := (19978312896157543819/3125000000000000000)
  directionHi := (639306012677041402209/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree165.table
  base := (121459434062554574840128180908213736158497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-7895383604967980034377751806086408127000000000000)
      constant := (359185663788625251236342843246735625176371832828033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree165.table
  base := (242918868125109149660847715976133462114093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15794944923211437359260915202876660629000000000000)
      constant := (718735415541541259127658544293851249315289330278477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19978312896157543819/3125000000000000000)
  centralHi := (639306012677041402209/100000000000000000000)
  directionLo := (128250430840742468773/20000000000000000000)
  directionHi := (320626077101856171933/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree166.table
  base := (123477329965381360046313750681480022958217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-7943213611272059612572617379025827854500000000000)
      constant := (363618481738747044696076576719894539011862886371113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree166.table
  base := (246954659930762720077224805036576783507189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15890630255293993347714315509911280959000000000000)
      constant := (727605477037509928630528493859699724177422684166421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128250430840742468773/20000000000000000000)
  centralHi := (320626077101856171933/50000000000000000000)
  directionLo := (80399050901657291347/12500000000000000000)
  directionHi := (643192407213258330777/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree167.table
  base := (251022757042912034768922738073835372599073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-15982087235152278381534965903930495164000000000000)
      constant := (736157136730872175161518592217435044316458421253697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree167.table
  base := (125511378521456017378349802916178882164933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9004283208)
      previous := (4502141604)
      next := (4502141604)
      square := (45303629148763674881956672815604020000000000000)
      linear := (-7993157793688274668083857908472950644500000000000)
      constant := (368265051310788488903043096481859424540762734699237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80399050901657291347/12500000000000000000)
  centralHi := (643192407213258330777/100000000000000000000)
  directionLo := (161281706208940157767/25000000000000000000)
  directionHi := (645126824835760631069/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree168.table
  base := (51024631892311923135682499766051277067949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-16077747247760437537924697049809334619000000000000)
      constant := (745131847337385075176970236114984251734075601090305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree168.table
  base := (51024631892311923133742584811413653863963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-16082000919459105324621116123980521619000000000000)
      constant := (745509292293742722050541182381697513206250441474535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell140.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161281706208940157767/25000000000000000000)
  centralHi := (645126824835760631069/100000000000000000000)
  directionLo := (323527729703558189591/50000000000000000000)
  directionHi := (647055459407116379183/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree169.table
  base := (202543646239615570414392160284115018697/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2251070802)
      previous := (1125535401)
      next := (1125535401)
      square := (11325907287190918720489168203901005000000000000)
      linear := (-2021675907546074586789303524461021759250000000000)
      constant := (94270136912129137249868937158698917728902906283280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree169.table
  base := (259255867186707930122725213171946643095957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (18008566416)
      previous := (9004283208)
      next := (9004283208)
      square := (90607258297527349763913345631208040000000000000)
      linear := (-16177686251541661313074516431015141949000000000000)
      constant := (754543046054007469924353791289206465236845760385973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell140.Kernel169
