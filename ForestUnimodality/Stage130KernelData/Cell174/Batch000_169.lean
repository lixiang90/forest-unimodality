import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell174.Parameters
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch000_049
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch050_099
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch100_149
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch150_199
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree000.table
  base := (439709746285430178264164169/5000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78666336249587926615634003750000000000)
      linear := (-6090407607148790383733150125000000000)
      constant := (109927436571357544566041042250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree000.table
  base := (439709746285430178264164169/5000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78666336249587926615634003750000000000)
      linear := (-6090407607148790383733150125000000000)
      constant := (109927436571357544566041042250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree001.table
  base := (239314323578288122331680138221306358274963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-859713436025499958619798535354313500000000000)
      constant := (575688008154938875562125525206095898934570206391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree001.table
  base := (478524126933170280167342043936190535665879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-191093974476836552549869480197621750000000000)
      constant := (127902769943145629201164101367227283508897390067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49912617763438063261/100000000000000000000)
  directionHi := (24956308881719031631/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree002.table
  base := (55548456033241379011079211225108923336713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-3321695886145016842809288283296297000000000000)
      constant := (669667704639436399761297468176531565858783005705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree002.table
  base := (69409442075327721759166298780279756967873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-92292602295168748728548466262117625000000000)
      constant := (18594925542354396976889031995235655125565033029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49912617763438063261/100000000000000000000)
  centralHi := (24956308881719031631/50000000000000000000)
  directionLo := (70587100974598367371/100000000000000000000)
  directionHi := (17646775243649591843/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree003.table
  base := (43518197918607026228074922247554874389833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-136776802784417604677193874885665750000000000)
      constant := (11738088182576345086960464491419985705354852109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree003.table
  base := (10874515971951204583479856592656391623087/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-68405855485564179659814781237414906250000000)
      constant := (5866382856931386494599509579178736092722233602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70587100974598367371/100000000000000000000)
  centralHi := (17646775243649591843/25000000000000000000)
  directionLo := (5403199369064974217/6250000000000000000)
  directionHi := (86451189905039587473/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree004.table
  base := (1846514229345768612162103321408830641713/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-815779239291631336743583838558954625000000000)
      constant := (36399657839548375814466531475157820900763889128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree004.table
  base := (118119459252704032601415867590707831175857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-725323278588351879642842634750168000000000000)
      constant := (32340303456993612709954544719591906003747242261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5403199369064974217/6250000000000000000)
  centralHi := (86451189905039587473/100000000000000000000)
  directionLo := (49912617763438063261/50000000000000000000)
  directionHi := (99825235526876126523/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree005.table
  base := (86159608476315330430645214840522691894867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-8128502928427067619518361921059307000000000000)
      constant := (218089010542174140291284089783302132454645708919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree005.table
  base := (86118971500439441921344601952641452109997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-903399713292190322007167019601016750000000000)
      constant := (24221880292755560799320797446020196520521728481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49912617763438063261/50000000000000000000)
  centralHi := (99825235526876126523/100000000000000000000)
  directionLo := (2790200156350275669/2500000000000000000)
  directionHi := (111608006254011026761/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree006.table
  base := (13280334092958056424673741376267185871619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-1081196882502342727232005903738553000000000000)
      constant := (19478594915454169431031399148915017254390315435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree006.table
  base := (3318604773094529159765702747866283772499/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-270369036999007191092872851112966375000000000)
      constant := (4867897818474521137830874493477270288936876635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2790200156350275669/2500000000000000000)
  centralHi := (111608006254011026761/100000000000000000000)
  directionLo := (122260445246998987667/100000000000000000000)
  directionHi := (30565111311749746917/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree007.table
  base := (831189698116971766401417026720378813979/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-1416630119576887683832218043279330875000000000)
      constant := (18641199111879506922026695802237108733439218424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree007.table
  base := (26586791405437976479593825900697198758817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-629776291349933603367907894651357125000000000)
      constant := (8282574044685146570469442601659413945708164341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122260445246998987667/100000000000000000000)
  centralHi := (30565111311749746917/25000000000000000000)
  directionLo := (33014093471570507299/25000000000000000000)
  directionHi := (132056373886282029197/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree008.table
  base := (5461720509017519045762544763160690130277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-1616913746338639799528429444852789625000000000)
      constant := (16588066292366726459117150093148954077588472289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree008.table
  base := (5459459951427349915046388862851218795899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-179703627175463206137517521769195375000000000)
      constant := (1842713472104433729345858392641454179356723527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33014093471570507299/25000000000000000000)
  centralHi := (132056373886282029197/100000000000000000000)
  directionLo := (141174201949196734743/100000000000000000000)
  directionHi := (17646775243649591843/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree009.table
  base := (36434925776853116978050202101403387009517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-1615286553867015035755236307934443000000000000)
      constant := (13613604380853243155906402044673719117493685441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree009.table
  base := (1820990297508306861965733998819693717213/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-403926363026886022866116139751102937500000000)
      constant := (3402894291275839390208954455014918372154119245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141174201949196734743/100000000000000000000)
  centralHi := (17646775243649591843/12500000000000000000)
  directionLo := (18717231661289273723/12500000000000000000)
  directionHi := (29947570658062837957/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree010.table
  base := (15321235522096712406348917959210630027943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-8069923999448576123683408991998828500000000000)
      constant := (58357303634221518253993575382212482408100536251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree010.table
  base := (1531472315230213113932121144525770086937/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-448445471702845633457197235963815125000000000)
      constant := (3241823068119350590874674064001650161873595505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18717231661289273723/12500000000000000000)
  centralHi := (29947570658062837957/20000000000000000000)
  directionLo := (78918778056921802741/50000000000000000000)
  directionHi := (157837556113843605483/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree011.table
  base := (6469951543720477192053720174946585824041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-4435529253247792293234127299146331750000000000)
      constant := (28557804856366934944638664163525021819298554837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree011.table
  base := (6467094163237313735193561564635887108741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-492964580378805244048278332176527312500000000)
      constant := (3173076454596382279707134039646527106738034193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78918778056921802741/50000000000000000000)
  centralHi := (157837556113843605483/100000000000000000000)
  directionLo := (20692678178218996633/12500000000000000000)
  directionHi := (33108285085150394613/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree012.table
  base := (4376923246095311551643306478118619116097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-2149376225231687344278466712130333000000000000)
      constant := (12715724964146443484779550087470815125524918905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree012.table
  base := (10937243124212478018573193926666704224151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-1074967378109529709278718856778479000000000000)
      constant := (6358294444139655523969595741142605430179095123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20692678178218996633/12500000000000000000)
  centralHi := (33108285085150394613/20000000000000000000)
  directionLo := (34580475962015834989/20000000000000000000)
  directionHi := (86451189905039587473/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree013.table
  base := (18487203896455772470042234994779484649797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-20946655041179203024075891621760667000000000000)
      constant := (116937476158479677982917904619613779271061924929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree013.table
  base := (9239093361739736888594163885623628402929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-1164005595461448930460881049203903375000000000)
      constant := (6497416024617403282734282356444653026764499717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34580475962015834989/20000000000000000000)
  centralHi := (86451189905039587473/50000000000000000000)
  directionLo := (179962502638710677609/100000000000000000000)
  directionHi := (17996250263871067761/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree014.table
  base := (1556975085384206691921876759035775440207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-11274462027636609974822791417174168500000000000)
      constant := (60717886502663626435946771735358651925889116495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree014.table
  base := (972607280472998143825897200807239066009/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-313260953203342037910760810407331937500000000)
      constant := (1686946572977672463241355679874813555809395114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179962502638710677609/100000000000000000000)
  centralHi := (17996250263871067761/10000000000000000000)
  directionLo := (37351182989558454141/20000000000000000000)
  directionHi := (93377957473896135353/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree015.table
  base := (6522743076747386340162456551812437515589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-1341732948298179826400848558163111500000000000)
      constant := (7095987195817104321273183437636431868352459897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree015.table
  base := (50930991814289858099945648098279369513/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (396557001034172738069411012903750000000000)
      linear := (-6330575613987204588798138839880906250000000)
      constant := (33480272332221588902489904767292429740818556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37351182989558454141/20000000000000000000)
  centralHi := (93377957473896135353/50000000000000000000)
  directionLo := (193310737363412106421/100000000000000000000)
  directionHi := (96655368681706053211/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree016.table
  base := (2711908006995445752065061103972919939937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-6438365520865313450196241314880919250000000000)
      constant := (33913223692124577104327683027148830452015092909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree016.table
  base := (10841276763584780646658494954500893954087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-2862240495034413188014735252960353000000000000)
      constant := (15077183644273140721490123017612550340395286051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193310737363412106421/100000000000000000000)
  centralHi := (96655368681706053211/50000000000000000000)
  directionLo := (39930094210750450609/20000000000000000000)
  directionHi := (99825235526876126523/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree017.table
  base := (8923226946652911466356197408713328560069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-27355731097555270726354656472111347000000000000)
      constant := (145083799717442924427477381633180579182413834433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree017.table
  base := (8917592555600594865711404540248172675607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-3040316929738251630379059637811201750000000000)
      constant := (16126069629275146340324401565364656311697449011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39930094210750450609/20000000000000000000)
  centralHi := (99825235526876126523/50000000000000000000)
  directionLo := (205794995089735452903/100000000000000000000)
  directionHi := (25724374386216931613/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree018.table
  base := (112960022835183512768037985647261790039/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-402194445995128995165615940065264125000000000)
      constant := (2165520812811271402338807422078824368840717976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree018.table
  base := (7224457970420900333788452859980419100821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-3218393364442090072743384022662050500000000000)
      constant := (17330852191642698708913733210612715481173649033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205794995089735452903/100000000000000000000)
  centralHi := (25724374386216931613/12500000000000000000)
  directionLo := (105880651461897551057/50000000000000000000)
  directionHi := (42352260584759020423/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree019.table
  base := (57312154202150637038186810901286806809/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-7640067281435826144373509724321671750000000000)
      constant := (42017421762274755948261213274027760758005715325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree019.table
  base := (1431704463933696922368976493771032147421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-849117449786482128776927101878224812500000000)
      constant := (4670541385291858810110281603943885493407285833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105880651461897551057/50000000000000000000)
  centralHi := (42352260584759020423/20000000000000000000)
  directionLo := (27195507104799953793/12500000000000000000)
  directionHi := (43512811367679926069/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree020.table
  base := (4399632149833687444982836293966584155267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-32162538139837321503063730109874357000000000000)
      constant := (181470833508763980729785885645958297696636351719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree020.table
  base := (1098940040869297989427908788604295712769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-893636558462441739368008198090937000000000000)
      constant := (5043071289807917082581076765341925654717632037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27195507104799953793/12500000000000000000)
  centralHi := (43512811367679926069/20000000000000000000)
  directionLo := (223216012508022053521/100000000000000000000)
  directionHi := (111608006254011026761/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree021.table
  base := (3210730971493216361358304088877255041263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-3751645239325704269848157924718003000000000000)
      constant := (21784813675937610592109565741441500861139359499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree021.table
  base := (1603664372744478794540271034511355080619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-1876311334276802699918178588607298375000000000)
      constant := (10897405304931635956479697540773401563922970087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223216012508022053521/100000000000000000000)
  centralHi := (111608006254011026761/50000000000000000000)
  directionLo := (57182087258588096867/25000000000000000000)
  directionHi := (228728349034352387469/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree022.table
  base := (214459984993719374185625900655818416173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-17683538084012677677101556267524848500000000000)
      constant := (105899638074681203905399929137785798316688501805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree022.table
  base := (85664642451187786269700552490439318997/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-3930699103257443842200681562065445500000000000)
      constant := (23544423135746807040422736990707187573109637025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57182087258588096867/25000000000000000000)
  centralHi := (228728349034352387469/100000000000000000000)
  directionLo := (117055464485836375277/50000000000000000000)
  directionHi := (46822185794334550111/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree023.table
  base := (18510313479133031797340719467509087977/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-4621168147764921534971600468454670875000000000)
      constant := (28579853527911828414219586743827438375469689512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree023.table
  base := (591023907773507369808386185323032941799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-2054387768980641142282502973458147125000000000)
      constant := (12708347266341724345544459042325889066878014227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117055464485836375277/50000000000000000000)
  centralHi := (46822185794334550111/20000000000000000000)
  directionLo := (119686252840477335797/50000000000000000000)
  directionHi := (47874501136190934319/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree024.table
  base := (79272648486973198340466985833196451737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-1071433727672594144592847082228473250000000000)
      constant := (6848576274586694498016341054008635595599929501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree024.table
  base := (3148072937295321561081290363269132477/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-1071712993166280181732332582941785750000000000)
      constant := (6851983336898421942062276752684471848281938025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119686252840477335797/50000000000000000000)
  centralHi := (47874501136190934319/20000000000000000000)
  directionLo := (122260445246998987667/50000000000000000000)
  directionHi := (48904178098799595067/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree025.table
  base := (-93928214200310695161258294150076496419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-40173883210307406130912186172812707000000000000)
      constant := (265501298545678318330837597589012672550001093085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree025.table
  base := (-471633900855241093972337663127643540331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-4464928407368959169293654716617991750000000000)
      constant := (29515059504150673905428829052411662740836645737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122260445246998987667/50000000000000000000)
  centralHi := (48904178098799595067/20000000000000000000)
  directionLo := (249563088817190316307/100000000000000000000)
  directionHi := (62390772204297579077/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree026.table
  base := (-1185164518286992076337232062909506978907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-41776152224401423056481877385400377000000000000)
      constant := (285473331316295102857830807519619471627320320801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree026.table
  base := (-1186901464105087008451390469839100643913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-4643004842072797611657979101468840500000000000)
      constant := (31735501276304308992922714527572277682413832051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249563088817190316307/100000000000000000000)
  centralHi := (62390772204297579077/25000000000000000000)
  directionLo := (127252705975134272587/50000000000000000000)
  directionHi := (10180216478010741807/4000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree027.table
  base := (-1837524853800976114650156958691751275377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-4819824582055048886894618733109783000000000000)
      constant := (34049499920142408409961763102908329736503700779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree027.table
  base := (-114939804361441641098056948501957404387/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-602635159597079506752787935789961156250000000)
      constant := (4258388774923111852785095437268238345162611598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127252705975134272587/50000000000000000000)
  centralHi := (10180216478010741807/4000000000000000000)
  directionLo := (129676784857559381209/50000000000000000000)
  directionHi := (259353569715118762419/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree028.table
  base := (-1216723279792113959526368546338077502223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-22490345126294728453810629905287858500000000000)
      constant := (164200816520137821833362135254620294375487169789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree028.table
  base := (-304345155311028650719156941989543611807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-624894713935059312048328483896317250000000000)
      constant := (4563511321296241163810944859026556680227688389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129676784857559381209/50000000000000000000)
  centralHi := (259353569715118762419/100000000000000000000)
  directionLo := (33014093471570507299/12500000000000000000)
  directionHi := (264112747772564058393/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree029.table
  base := (-2978552579522512792428442190494010364729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-46582959266683473833190951023163387000000000000)
      constant := (351328211904195882629630447955761531919418329947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree029.table
  base := (-744923612198209803807617118992518958727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-1294308536546078234687738064005346687500000000)
      constant := (9764235228161925284566770387157644097474406229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33014093471570507299/12500000000000000000)
  centralHi := (264112747772564058393/100000000000000000000)
  directionLo := (268787672611623157899/100000000000000000000)
  directionHi := (2687876726116231579/1000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree030.table
  base := (-54336664006148088716349761023772231841/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-669239281677465149427231142163209125000000000)
      constant := (5211304525557629474692902283780348737018756056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree030.table
  base := (-1739268635583213474609816193106097910637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-2677655290444075690557638320436117750000000000)
      constant := (20856202652031739194867549814005771612296380799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268787672611623157899/100000000000000000000)
  centralHi := (2687876726116231579/1000000000000000000)
  directionLo := (273382666531680802487/100000000000000000000)
  directionHi := (34172833316460100311/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree031.table
  base := (-1967182089719651856629794430983204878549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-24893748647435753842165166724169363500000000000)
      constant := (200024655413099295480483454934511181326850852207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree031.table
  base := (-245951440389618716705309073995793855443/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-691673376948998727934950128215385531250000000)
      constant := (5559179107908896846383333457524904336324142222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273382666531680802487/100000000000000000000)
  centralHi := (34172833316460100311/12500000000000000000)
  directionLo := (55580338887765432431/20000000000000000000)
  directionHi := (69475423609706790539/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree032.table
  base := (-4352300122794012378590215761486513233729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-51389766308965524609900024660926397000000000000)
      constant := (425826445063412268691167092334154938198244296947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree032.table
  base := (-4353043989676212683709014701882231518781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-5711463450295828265843925410573933000000000000)
      constant := (47339143999130662247775158462694164558432723887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55580338887765432431/20000000000000000000)
  centralHi := (69475423609706790539/25000000000000000000)
  directionLo := (141174201949196734743/50000000000000000000)
  directionHi := (282348403898393469487/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree033.table
  base := (-946822553976078422920809847105754422069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3172456008273381904555288103230000000000000)
      linear := (-111094413675177235923416595122671000000000000)
      constant := (948718439659012548141985452736247459791750855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree033.table
  base := (-946951300891947453362606567363891040267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-5889539884999666708208249795424781750000000000)
      constant := (50308802275192206669293194232863628718931224045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141174201949196734743/50000000000000000000)
  centralHi := (282348403898393469487/100000000000000000000)
  directionLo := (286726159594776781591/100000000000000000000)
  directionHi := (35840769949347097699/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree034.table
  base := (-1270528092499603565225345711784042760041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-13648576084288389615259851771525434250000000000)
      constant := (120045126915470687523552888160764428243044093163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree034.table
  base := (-2541334509909677935914019832135501522811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-3033808159851752575286287090137815250000000000)
      constant := (26690895470745918365987366150304475386021016697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286726159594776781591/100000000000000000000)
  centralHi := (35840769949347097699/12500000000000000000)
  directionLo := (18189879570275523639/6250000000000000000)
  directionHi := (11641522924976335129/4000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree035.table
  base := (-215929372074221906795175710879244480171/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-56196573351247575386609098298689407000000000000)
      constant := (508747227168594867401306970644311658262336518825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree035.table
  base := (-2699357648319966860386962590803833440491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-3122846377203671796468449282563239625000000000)
      constant := (28278796674666330169928526297831292076172448057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18189879570275523639/6250000000000000000)
  centralHi := (11641522924976335129/4000000000000000000)
  directionLo := (295287028871854700089/100000000000000000000)
  directionHi := (29528702887185470009/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree036.table
  base := (-1421025074187053313264570210805530976179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-1605523399037266453116077486424363250000000000)
      constant := (14950970963670678039090862027767158372501328033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree036.table
  base := (-5684515632590663476980434863924475902587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-6423769189111182035301222949977328000000000000)
      constant := (59835776598925506281500357030206964624678123449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295287028871854700089/100000000000000000000)
  centralHi := (29528702887185470009/10000000000000000000)
  directionLo := (18717231661289273723/6250000000000000000)
  directionHi := (299475706580628379569/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree037.table
  base := (-2970534790209708728775303707532526254363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-29700555689717804618874240361932373500000000000)
      constant := (284320210948378224879327051460673848267387667809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree037.table
  base := (-2970713993243640084348070276918243367663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-3300922811907510238832773667414088375000000000)
      constant := (31607988940169849091101194959667549832700123301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18717231661289273723/6250000000000000000)
  centralHi := (299475706580628379569/100000000000000000000)
  directionLo := (303606601120538380529/100000000000000000000)
  directionHi := (30360660112053838053/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree038.table
  base := (-6170281610908182872723149134727486530959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-61003380393529626163318171936452417000000000000)
      constant := (599960888890627050415036172054998060169576819837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree038.table
  base := (-192830959359299412189881371106455213123/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-847490257314857365003733964959878187500000000)
      constant := (8337236632443801513596816783307655098970904884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303606601120538380529/100000000000000000000)
  centralHi := (30360660112053838053/10000000000000000000)
  directionLo := (307682039865775672011/100000000000000000000)
  directionHi := (76920509966443918003/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree039.table
  base := (-6372691806959813194376104570943607057593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-6956183267513738120987540349893343000000000000)
      constant := (70243784257213806684172778036747670671601705411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree039.table
  base := (-6372958207945652613117438672774360140681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-6957998493222697362394196104529874250000000000)
      constant := (70281267136941633013103185326405066901571335187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307682039865775672011/100000000000000000000)
  centralHi := (76920509966443918003/25000000000000000000)
  directionLo := (31170419802749504003/10000000000000000000)
  directionHi := (311704198027495040031/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree040.table
  base := (-6549101427302310361848288699150967798471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-64207918421717660014457554361627757000000000000)
      constant := (665338003497364850826959870827647426323411967653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree040.table
  base := (-6549330908122172525895740644900923774869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-7136074927926535804758520489380723000000000000)
      constant := (73965886268235191558362841817588055492296924663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31170419802749504003/10000000000000000000)
  centralHi := (311704198027495040031/100000000000000000000)
  directionLo := (63135022445537442193/20000000000000000000)
  directionHi := (157837556113843605483/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree041.table
  base := (-6700182566797086365793006846549677106811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-65810187435811676940027245574215427000000000000)
      constant := (699391108347545150191241437648096920065077862273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree041.table
  base := (-837547517393683057613823207292819715847/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-914268920328796780890355609278946468750000000)
      constant := (9718946386217969899925627659289345027862696969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63135022445537442193/20000000000000000000)
  centralHi := (157837556113843605483/50000000000000000000)
  directionLo := (63919338510958321271/20000000000000000000)
  directionHi := (79899173138697901589/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree042.table
  base := (-6826499074180984690567072930370813815273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-7490272938878410429510770754089233000000000000)
      constant := (81594668562115337788020570598855789560532066771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree042.table
  base := (-3413334544307465138926706195055555095897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-3746113898667106344743584629541210250000000000)
      constant := (40819085566475023509585191475465947287738910819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63919338510958321271/20000000000000000000)
  centralHi := (79899173138697901589/25000000000000000000)
  directionLo := (32347073330358816479/10000000000000000000)
  directionHi := (323470733303588164791/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree043.table
  base := (-6928524062121005398535676011659438880849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-69014725463999710791166627999390767000000000000)
      constant := (770219592005468296860830312139403655622982371107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree043.table
  base := (-216520946614387964798351962078378728893/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-958788029004756391481436705491658656250000000)
      constant := (10703195018652825361380003032690029712079069544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32347073330358816479/10000000000000000000)
  centralHi := (323470733303588164791/100000000000000000000)
  directionLo := (327298922570729117843/100000000000000000000)
  directionHi := (81824730642682279461/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree044.table
  base := (-56053236551245780306753235662092780447/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-70616994478093727716736319211978437000000000000)
      constant := (806992878485639861748488479008631064265837877625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree044.table
  base := (-3503390141398690013267944958099582620387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-3924190333370944787107909014392059000000000000)
      constant := (44856816097623198018627537533732600275063344049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327298922570729117843/100000000000000000000)
  centralHi := (81824730642682279461/25000000000000000000)
  directionLo := (331082850851503946129/100000000000000000000)
  directionHi := (33108285085150394613/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree045.table
  base := (-7061223838427053097123208150347808110269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-8024362610243082738034001158285123000000000000)
      constant := (93852341688402190946703955742446035063755100463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree045.table
  base := (-7061331867034790928198524687117396820317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-8026457101445728016580142413634966750000000000)
      constant := (93902298354508766200739172109401559950262946159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331082850851503946129/100000000000000000000)
  centralHi := (33108285085150394613/10000000000000000000)
  directionLo := (167412009381016540141/50000000000000000000)
  directionHi := (334824018762033080283/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree046.table
  base := (-7092511607967847807835504997351128025533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-73821532506281761567875701637153777000000000000)
      constant := (883253509491166227466471166302857620648308446119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree046.table
  base := (-7092604399761423038859597406736886162131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-8204533536149566458944466798485815500000000000)
      constant := (98191483990792428075431056368790545632154974337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167412009381016540141/50000000000000000000)
  centralHi := (334824018762033080283/100000000000000000000)
  directionLo := (84630960998309209591/25000000000000000000)
  directionHi := (67704768798647367673/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree047.table
  base := (-7100752729064745212220705040919553569207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-75423801520375778493445392849741447000000000000)
      constant := (922739616658373003624885281139193720028288323701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree047.table
  base := (-710083240057536494191169025644055062701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-4191304985426702450654395591668332125000000000)
      constant := (51290563223396400770119990743242769707883678635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84630960998309209591/25000000000000000000)
  centralHi := (67704768798647367673/20000000000000000000)
  directionLo := (342183667587973032327/100000000000000000000)
  directionHi := (42772958448496629041/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree048.table
  base := (-7086144393178218512603299789357524499431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-8558452281607755046557231562481013000000000000)
      constant := (107014324726570380659290685984809846106913521437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree048.table
  base := (-7086212772716006963390177931765001962469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-8560686405557243343673115568187513000000000000)
      constant := (107071173115280708963588098298955938130681269863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342183667587973032327/100000000000000000000)
  centralHi := (42772958448496629041/12500000000000000000)
  directionLo := (34580475962015834989/10000000000000000000)
  directionHi := (345804759620158349891/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree049.table
  base := (-3524426094632461160380605631088653807413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-39314169774281906172292387637458393500000000000)
      constant := (502210514482681323924665479818834973866808418959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree049.table
  base := (-1762227713779760936123821803410664990129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-2184690710065270446509359988259590437500000000)
      constant := (27915394955539171000275504654114921095951639683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34580475962015834989/10000000000000000000)
  centralHi := (345804759620158349891/100000000000000000000)
  directionLo := (34938832434406644283/10000000000000000000)
  directionHi := (349388324344066442831/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree050.table
  base := (-109203362236146478433844076312034045817/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-10028826070332228658769308310938057125000000000)
      constant := (130826950193180678492026123230845849182139295448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree050.table
  base := (-3494532748442183861123145127095702040383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-4458419637482460114200882168944605250000000000)
      constant := (58176154735345080545352996220149493983139752741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34938832434406644283/10000000000000000000)
  centralHi := (349388324344066442831/100000000000000000000)
  directionLo := (176467752436495918429/50000000000000000000)
  directionHi := (352935504872991836859/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree051.table
  base := (-6906750177230553151994137238252564549857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-9092541952972427355080461966676903000000000000)
      constant := (121079151046788443923886095844024960571521055739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree051.table
  base := (-1726698328219387373994360030939115660969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-2273728927417189667691522180685014812500000000)
      constant := (30285832726134415284666022343727625797996304363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176467752436495918429/50000000000000000000)
  centralHi := (352935504872991836859/100000000000000000000)
  directionLo := (71289477487761885689/20000000000000000000)
  directionHi := (178223693719404714223/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree052.table
  base := (-3401077642061686929209845617066859410327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-41717573295422931560646924456339898500000000000)
      constant := (566855533337599528855673828294814240736882339861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree052.table
  base := (-1700548063311686367196588824524191792941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-2318248036093149278282603276897727000000000000)
      constant := (31508654488516062688572877349817572262354574207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71289477487761885689/20000000000000000000)
  centralHi := (178223693719404714223/50000000000000000000)
  directionLo := (359925005277421355219/100000000000000000000)
  directionHi := (17996250263871067761/5000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree053.table
  base := (-6675312924149281576793347571851999782919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28552104074460437140997592929070000000000000)
      linear := (-1604479539715846793337047926891839000000000000)
      constant := (22237953304213342993181134769195608621848747889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree053.table
  base := (-6675344597972100105134331088144733046549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3172456008273381904555288103230000000000000)
      linear := (-178322048661819538782919575329089750000000000)
      constant := (2472191483703411222652542167193784892899846491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359925005277421355219/100000000000000000000)
  centralHi := (17996250263871067761/5000000000000000000)
  directionLo := (363369342179483908229/100000000000000000000)
  directionHi := (36336934217948390823/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree054.table
  base := (-6526292341003034122187279346410377189479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-9626631624337099663603692370872793000000000000)
      constant := (136045952029445491369910646867626657295155327133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree054.table
  base := (-130526389389250775793128913700762700787/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-4814572506890136998929530938646302750000000000)
      constant := (68058952241772966727877329007675290657940871225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363369342179483908229/100000000000000000000)
  centralHi := (36336934217948390823/10000000000000000000)
  directionLo := (183390667870498481501/50000000000000000000)
  directionHi := (366781335740996963003/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree055.table
  base := (-3177575856385383426886437590949668137081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-44120976816563956949001461275221403500000000000)
      constant := (635558528103890762701145808498834656333304921883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree055.table
  base := (-3177587470541854162098758755145580024073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-4903610724242056220111693131071727125000000000)
      constant := (70654934990112173383405996594689512584947094371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183390667870498481501/50000000000000000000)
  centralHi := (366781335740996963003/100000000000000000000)
  directionLo := (370161880344193476871/100000000000000000000)
  directionHi := (46270235043024184609/12500000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree056.table
  base := (-3080969961912755393825828184224768406177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-44922111323610965411786306881515238500000000000)
      constant := (659360935703181062758451751302811369555548251411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree056.table
  base := (-1232391961369709811187854948612205738387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-9985297883187950882587710646994303000000000000)
      constant := (146602032089873215422379156520545958781289650245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370161880344193476871/100000000000000000000)
  centralHi := (46270235043024184609/12500000000000000000)
  directionLo := (373511829895584541411/100000000000000000000)
  directionHi := (93377957473896135353/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree057.table
  base := (-1486674513062714136982069041648927688233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-2540180323925442993031730693767170750000000000)
      constant := (37978553196837716062575174052841905042751724691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree057.table
  base := (-5946715066918870800506369457902621431199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-10163374317891789324952035031845151750000000000)
      constant := (151994379858356308208586262840136331072799769573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373511829895584541411/100000000000000000000)
  centralHi := (93377957473896135353/25000000000000000000)
  directionLo := (94208000086227800037/25000000000000000000)
  directionHi := (376832000344911200149/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree058.table
  base := (-1141892123724038683549798128839045039863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-93048760675409964674711996188205817000000000000)
      constant := (1416635104240482096395185594835967932880410721545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree058.table
  base := (-1141895034942221072848518767208984600063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-10341450752595627767316359416696000500000000000)
      constant := (157486904080650996790437022159714650505986840505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94208000086227800037/25000000000000000000)
  centralHi := (376832000344911200149/100000000000000000000)
  directionLo := (95030793001514194641/25000000000000000000)
  directionHi := (76024634401211355713/20000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree059.table
  base := (-1362564158635885219904471550816902103213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-23662757422375995400070421850198371750000000000)
      constant := (366735842277316281581887477730004980579404458359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree059.table
  base := (-1090053816797547983543312135563284278503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-10519527187299466209680683801546849250000000000)
      constant := (163079597021093696183109106491578753958235089905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95030793001514194641/25000000000000000000)
  centralHi := (76024634401211355713/20000000000000000000)
  directionLo := (191693045849311719791/50000000000000000000)
  directionHi := (383386091698623439583/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree060.table
  base := (-2584555241592660121593150809357115322691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-5347405483533222140325076589632286500000000000)
      constant := (84341813947877676479929328885772446427890677457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree060.table
  base := (-646140141013835823247409004678893774143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-1337200452750413081505626023299712250000000000)
      constant := (21096556522308388029802033057987264429305892261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191693045849311719791/50000000000000000000)
  centralHi := (383386091698623439583/100000000000000000000)
  directionLo := (386621474726824212843/100000000000000000000)
  directionHi := (96655368681706053211/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree061.table
  base := (-60825533234458571521185989914953018681/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-12231945964711501931427633728246103375000000000)
      constant := (196282862602322794623399042846782535892594706830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree061.table
  base := (-2433025879218110465312153687117000015667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-5437840028353571547204666285624273375000000000)
      constant := (87282732044360505372870427335890591235282950609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386621474726824212843/100000000000000000000)
  centralHi := (96655368681706053211/25000000000000000000)
  directionLo := (12182187709704526709/3125000000000000000)
  directionHi := (389830006710544854689/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree062.table
  base := (-113526759690754077247956459140607434187/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-12432229591473254047123845129819562125000000000)
      constant := (202909259619727878239191049590722498174368049205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree062.table
  base := (-4541078164478054189274868633114240680239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-11053756491410981536773656956099395500000000000)
      constant := (180458628159281468932593373382006054193488505653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12182187709704526709/3125000000000000000)
  centralHi := (389830006710544854689/100000000000000000000)
  directionLo := (393012345281853098343/100000000000000000000)
  directionHi := (49126543160231637293/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree063.table
  base := (-2097104075037244884924474734232701284569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-5614450319215558294586691791730231500000000000)
      constant := (93177008036716034942695668729497625999697846563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree063.table
  base := (-4194214794817768329604651496159251822429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-11231832926114819979137981340950244250000000000)
      constant := (186451940529877591799924536298102399111283676783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393012345281853098343/100000000000000000000)
  centralHi := (49126543160231637293/12500000000000000000)
  directionLo := (99042280414711521897/25000000000000000000)
  directionHi := (396169121658846087589/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree064.table
  base := (-478183514818571636193517180651623214777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-12832796844996758278516267932966479625000000000)
      constant := (216499884332300986665516555663202550837545461211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree064.table
  base := (-3825473794685118906942738801149619309669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-11409909360818658421502305725801093000000000000)
      constant := (192545397955631909866750406371051864760177804263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99042280414711521897/25000000000000000000)
  centralHi := (396169121658846087589/100000000000000000000)
  directionLo := (399300942107504506091/100000000000000000000)
  directionHi := (99825235526876126523/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree065.table
  base := (-3434860525929167631547301529135612148387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-104264643774068083153699834676319507000000000000)
      constant := (1787712842344845388611651475139058839859311000441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree065.table
  base := (-3434865373568403067896818041016931461259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-11587985795522496863866630110651941750000000000)
      constant := (198738997708844806319520367910305439894138549193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399300942107504506091/100000000000000000000)
  centralHi := (99825235526876126523/25000000000000000000)
  directionLo := (402408389301142351329/100000000000000000000)
  directionHi := (40240838930114235133/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree066.table
  base := (-6044787949793571041343386360675830103/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-2940747577448947224424153496914088250000000000)
      constant := (51231317417626818628826269290447715305486397625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree066.table
  base := (-3022398114066787130640787382038906805843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-11766062230226335306230954495502790500000000000)
      constant := (205032737496477514095508946021084207620712508161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402408389301142351329/100000000000000000000)
  centralHi := (40240838930114235133/10000000000000000000)
  directionLo := (81098404717217171879/20000000000000000000)
  directionHi := (101373005896521464849/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree067.table
  base := (-1294037848950616498003434143758779618411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-53734590901128058502419608550747423500000000000)
      constant := (950921405668365165330789128122868974657092501073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree067.table
  base := (-323509903924368528786172407746347105173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-1493017333116271718574409860044204906250000000)
      constant := (26428326923852435282562016536724473684361801571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81098404717217171879/20000000000000000000)
  centralHi := (101373005896521464849/25000000000000000000)
  directionLo := (25534524010085489717/6250000000000000000)
  directionHi := (408552384161367835473/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree068.table
  base := (-213191177561574521499176457654239448331/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-54535725408175066965204454157041258500000000000)
      constant := (980129490315007288186341630363309907774197778165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree068.table
  base := (-1065957395719679861335867168072491763827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1586228004136690952277644051615000000000000)
      linear := (-114360519807868039537354747784948000000000000)
      constant := (2055854997841788906307405544642764631518548093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25534524010085489717/6250000000000000000)
  centralHi := (408552384161367835473/100000000000000000000)
  directionLo := (205794995089735452903/50000000000000000000)
  directionHi := (411589990179470905807/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree069.table
  base := (-165390732051988396224977044950988568559/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-6148539990580230603109922195926121500000000000)
      constant := (112198662367842760562495113719598948655861931465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree069.table
  base := (-1653909893997973958525145803135267810669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-12300291534337850633323927650055336750000000000)
      constant := (224514779275179621196371977500353449929157631263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205794995089735452903/50000000000000000000)
  centralHi := (411589990179470905807/100000000000000000000)
  directionLo := (207302670887241603321/50000000000000000000)
  directionHi := (414605341774483206643/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree070.table
  base := (-577033315593378400214050446351049384561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-56137994422269083890774145369628928500000000000)
      constant := (1039896813487015808058374157799226142245008155523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree070.table
  base := (-144258603346441625860432866742636759477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-1559795996130211134461031504363273187500000000)
      constant := (28901132844638950410380890123397030817654001479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207302670887241603321/50000000000000000000)
  centralHi := (414605341774483206643/100000000000000000000)
  directionLo := (417598921023432605407/100000000000000000000)
  directionHi := (13049966281982268919/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree071.table
  base := (-632393321956710692393203005950212541349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4770000000000000000000000000000000000000000
      center := (83952)
      previous := (41976)
      next := (41976)
      square := (300190739128427527965259358310000000000000)
      linear := (-22590410208020667468184483624647000000000000)
      constant := (424699877999943061431502243845388748617776527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree071.table
  base := (-632395194782283405451754240497649604809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (9328)
      previous := (4664)
      next := (4664)
      square := (33354526569825280885028817590000000000000)
      linear := (-2510701131471042951408961797214250000000000)
      constant := (47213544783547106061176778798465023008445123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417598921023432605407/100000000000000000000)
  centralHi := (13049966281982268919/3125000000000000000)
  directionLo := (42057119284603192537/10000000000000000000)
  directionHi := (420571192846031925371/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree072.table
  base := (-44445215964904699172365898789288273081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-6415584826262566757371537398024066500000000000)
      constant := (122385071632473579321568951776854827484216129987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree072.table
  base := (-44446014573430428972297446861407926127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-6417260419224682980208450402303941500000000000)
      constant := (122449013977797585699769253057935805060152871029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42057119284603192537/10000000000000000000)
  centralHi := (420571192846031925371/100000000000000000000)
  directionLo := (423522605847590204229/100000000000000000000)
  directionHi := (42352260584759020423/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree073.table
  base := (476439483420032228696693526820674962119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-117082795886820218558257364377020867000000000000)
      constant := (2265851233989683291175628576819657917724887976283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree073.table
  base := (47643812149859591759512194087479317641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-6506298636576602201390612594729365875000000000)
      constant := (125946354090693734714385269834948050507879244465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423522605847590204229/100000000000000000000)
  centralHi := (42352260584759020423/10000000000000000000)
  directionLo := (426453593109417148391/100000000000000000000)
  directionHi := (53306699138677143549/12500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree074.table
  base := (132949284404351818567176519152731102799/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-14835633112614279435478381948701067125000000000)
      constant := (291208989205767252224692499658428321517353055043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree074.table
  base := (1063593114150836185894940376810695055357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-13190673707857042845145549574309580500000000000)
      constant := (258987519358685248233393294728575935048774895761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426453593109417148391/100000000000000000000)
  centralHi := (53306699138677143549/12500000000000000000)
  directionLo := (429364572930663894147/100000000000000000000)
  directionHi := (107341143232665973537/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree075.table
  base := (418143034133841033695379327712454995719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-3341314830972451455816576300061005750000000000)
      constant := (66510925666914005203814475859157725988571232387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree075.table
  base := (836285573421128695482866814368558186849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-6684375071280440643754936979580214625000000000)
      constant := (133091230503025708767857744160644695776923757877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429364572930663894147/100000000000000000000)
  centralHi := (107341143232665973537/25000000000000000000)
  directionLo := (432255949525197937363/100000000000000000000)
  directionHi := (108063987381299484341/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree076.table
  base := (115168577389960423382339338380806238511/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-30472400732275567333741609503695969250000000000)
      constant := (615003865356050850460055499215672167032276473135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree076.table
  base := (2303370704338989028562924546763112403909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-13546826577264719729874198344011278000000000000)
      constant := (273477532718656398451506584037168657155289579257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432255949525197937363/100000000000000000000)
  centralHi := (108063987381299484341/25000000000000000000)
  directionLo := (27195507104799953793/6250000000000000000)
  directionHi := (435128113676799260689/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree077.table
  base := (147799561560406354457640027574759047343/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-30872967985799071565134032306842886750000000000)
      constant := (631634580704862228644115642589946062953009710255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree077.table
  base := (2955990512491726438295034140136948218631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-13724903011968558172238522728862126750000000000)
      constant := (280872734156081898806735809259817618577353800163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27195507104799953793/6250000000000000000)
  centralHi := (435128113676799260689/100000000000000000000)
  directionLo := (437981443355684434317/100000000000000000000)
  directionHi := (218990721677842217159/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree078.table
  base := (3630430112182890880886600858803188992431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-13899348995254478131789535604439913000000000000)
      constant := (288217989512305968679417682760379153412674767563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree078.table
  base := (226901843741198293023831184013835995783/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-1737872430834049576825355889214121937500000000)
      constant := (36046008129008466622031062759012343548846412918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437981443355684434317/100000000000000000000)
  centralHi := (218990721677842217159/50000000000000000000)
  directionLo := (220408152149556213737/50000000000000000000)
  directionHi := (17632652171964497099/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree079.table
  base := (4326687287043446090945023505260652451523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-126696409971384320111675511652546887000000000000)
      constant := (2662286207625167613445596703552114501676876790311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree079.table
  base := (1081671691361093231176431972736685863887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-3520263970344058764241792874640956062500000000)
      constant := (73990881276472960385201482698095668359421656451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220408152149556213737/50000000000000000000)
  centralHi := (17632652171964497099/4000000000000000000)
  directionLo := (354906440446877669/80000000000000000)
  directionHi := (443633050558597086251/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree080.table
  base := (5044761995818236705631469739864926259633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-128298678985478337037245202865134557000000000000)
      constant := (2731511227035295675755348994082975947492084347581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree080.table
  base := (2522380775784692943062032652010894483383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-7129566158040036749665747941707336500000000000)
      constant := (151829557087561567949922200599433814211808886259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354906440446877669/80000000000000000)
  centralHi := (443633050558597086251/100000000000000000000)
  directionLo := (446432025016044107043/100000000000000000000)
  directionHi := (111608006254011026761/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree081.table
  base := (578465359938214810543344057107437545527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-7216719333309575220156383004317901500000000000)
      constant := (155646497905795840933881383355466241056755425855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree081.table
  base := (5784653221069286770809680766910902858361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-14437208750783911941695820268265521750000000000)
      constant := (311454832069528351599285486963276544922814383453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446432025016044107043/100000000000000000000)
  centralHi := (111608006254011026761/25000000000000000000)
  directionLo := (449213559870942569353/100000000000000000000)
  directionHi := (224606779935471284677/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree082.table
  base := (3273180780116723444510368436315327585373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-65751608506833185444192292645154948500000000000)
      constant := (1436331706069901220523421041438962644652701744761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree082.table
  base := (654636123811717978619521987880261883911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-7307642592743875192030072326558185250000000000)
      constant := (159675339322974504704770795154140710525925768015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449213559870942569353/100000000000000000000)
  centralHi := (224606779935471284677/50000000000000000000)
  directionLo := (451977977100570661397/100000000000000000000)
  directionHi := (225988988550285330699/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree083.table
  base := (7329885426330073285155332768330449175523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-133105486027760387813954276502897567000000000000)
      constant := (2944590575454766689348931747734768980878148058311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree083.table
  base := (7329885152101700377198487261823618571539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-14793361620191588826424469037967219250000000000)
      constant := (327346653783993919228337735848189708730551289247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451977977100570661397/100000000000000000000)
  centralHi := (225988988550285330699/50000000000000000000)
  directionLo := (227362794447510172481/50000000000000000000)
  directionHi := (454725588895020344963/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree084.table
  base := (2033806204374515134687665245566502456319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-3741882084495955687208999103207923250000000000)
      constant := (83817179203751886353817311222768569660762116187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree084.table
  base := (1627044916814149901601836988255924536809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-14971438054895427268788793422818068000000000000)
      constant := (335442757382417311899979378842208413256364354785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227362794447510172481/50000000000000000000)
  centralHi := (454725588895020344963/100000000000000000000)
  directionLo := (57182087258588096867/12500000000000000000)
  directionHi := (457456698068704774937/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree085.table
  base := (8962379414002519876810988760446019692967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-136310024055948421665093658928072907000000000000)
      constant := (3091147039011885334268988151568884769774861650619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree085.table
  base := (71699033722661856892658219872894038237/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-15149514489599265711153117807668916750000000000)
      constant := (343638989356073397895618896038580895445674250125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57182087258588096867/12500000000000000000)
  centralHi := (457456698068704774937/100000000000000000000)
  directionLo := (460171598449883905757/100000000000000000000)
  directionHi := (230085799224941952879/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree086.table
  base := (9811348946936899386998233000969050576209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28552104074460437140997592929070000000000000)
      linear := (-2602118737170612048880440568691709000000000000)
      constant := (59731629015822978003716050307418093855592026121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree086.table
  base := (981134877787172538868552604699926675911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-7663795462151552076758721096259882750000000000)
      constant := (175967674816677779536608506244410310533290848015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460171598449883905757/100000000000000000000)
  centralHi := (230085799224941952879/50000000000000000000)
  directionLo := (462870575249626630171/100000000000000000000)
  directionHi := (115717643812406657543/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree087.table
  base := (5341066595070540767021915172722981928453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-7750809004674247528679613408513791500000000000)
      constant := (180072574848413917487836554293840722750770573369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree087.table
  base := (1068213304628775876162100067320722357783/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-7752833679503471297940883288685307125000000000)
      constant := (180165919077021504546809219576298423659198537295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462870575249626630171/100000000000000000000)
  centralHi := (115717643812406657543/25000000000000000000)
  directionLo := (116388476352880222987/25000000000000000000)
  directionHi := (465553905411520891949/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree088.table
  base := (1446841494175623865936574415562937630819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-17639603887278809055225341570729489625000000000)
      constant := (414717133356626550971332916893765890120749242183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree088.table
  base := (2314946366203881535293832118967949816167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-15683743793710781038246090962221463000000000000)
      constant := (368828454867490053474478830564328529281173929455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116388476352880222987/25000000000000000000)
  centralHi := (465553905411520891949/100000000000000000000)
  directionLo := (117055464485836375277/25000000000000000000)
  directionHi := (468221857943345501109/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree089.table
  base := (12489145076753138806319013959483966086069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-142719100112324489367372423778423587000000000000)
      constant := (3395068496198633331837021513060162095040019816433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree089.table
  base := (499565798905783348906981666672721434989/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-15861820228414619480610415347072311750000000000)
      constant := (377425199731103414588884851701982526747195402425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117055464485836375277/25000000000000000000)
  centralHi := (468221857943345501109/100000000000000000000)
  directionLo := (470874694231827972657/100000000000000000000)
  directionHi := (235437347115913986329/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree090.table
  base := (3356343106409526844566742499107000987737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-4008926920178291841470614305305868250000000000)
      constant := (96480573194021843102662181135776838524896657501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree090.table
  base := (1678171542135989493642646129396071145231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2004987082889807240371842466490395062500000000)
      constant := (48265259088632721669214917209487271730928551963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470874694231827972657/100000000000000000000)
  centralHi := (235437347115913986329/50000000000000000000)
  directionLo := (7398635442836419007/1562500000000000000)
  directionHi := (473512668341530816449/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree091.table
  base := (1797926735862295219474053487860864693637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-18240454767564065402313975775449865875000000000)
      constant := (444054185367421013312815766898217644350137703809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree091.table
  base := (14383413811590447516054038141893270645717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-16217973097822296365339064116774009250000000000)
      constant := (394919073771238980993218394273301450009165648041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7398635442836419007/1562500000000000000)
  centralHi := (473512668341530816449/100000000000000000000)
  directionLo := (476136027298833618949/100000000000000000000)
  directionHi := (9522720545976672379/2000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree092.table
  base := (15363269365358798228248068572098078424609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-147525907154606540144081497416186597000000000000)
      constant := (3632467039833524634403921370264087173162442543213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree092.table
  base := (7681634650660172590086911059504407327987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-8198024766263067403851694250812429000000000000)
      constant := (201908101446149266062143020408446323081540270751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476136027298833618949/100000000000000000000)
  centralHi := (9522720545976672379/2000000000000000000)
  directionLo := (119686252840477335797/25000000000000000000)
  directionHi := (478745011361909343189/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree093.table
  base := (3272987756194358214193683901197731069591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-16569797352077839674405687625419363000000000000)
      constant := (412600145052752984070044421285495081015279181215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree093.table
  base := (8182469363261315792673829821051318790337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-8287062983614986625033856443237853375000000000)
      constant := (206406730025466025090873424444022242225639457301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119686252840477335797/25000000000000000000)
  centralHi := (478745011361909343189/100000000000000000000)
  directionLo := (15041870446172811317/3125000000000000000)
  directionHi := (96267970855505992429/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree094.table
  base := (17388422066412770892521798268423175481923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-150730445182794573995220879841361937000000000000)
      constant := (3795236279701239008579808607078260218567286323111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree094.table
  base := (17388422020122185883422598046834063701821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-16752202401933811692432037271326555500000000000)
      constant := (421910845229218873903237249664567073520156622033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15041870446172811317/3125000000000000000)
  centralHi := (96267970855505992429/20000000000000000000)
  directionLo := (241960391762739161283/50000000000000000000)
  directionHi := (483920783525478322567/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree095.table
  base := (9216859582529023570288551233782688920501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-76166357098444295460395285526974803500000000000)
      constant := (1938985981188378099384353099108247008622613123057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree095.table
  base := (4608429781426976883115292819870963726983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-4232569709159412533699090414044351062500000000)
      constant := (107777089603021870080916546132122520841438604059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241960391762739161283/50000000000000000000)
  centralHi := (483920783525478322567/100000000000000000000)
  directionLo := (486488020551289551257/100000000000000000000)
  directionHi := (243244010275644775629/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree096.table
  base := (780033201171363553877449096737841878083/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-17103887023442511982928918029615253000000000000)
      constant := (440178705931868325826977226108575733702326733975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree096.table
  base := (9750414997918706773838110922594237104431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-8554177635670744288580343020514126500000000000)
      constant := (220202999793431272826919557125219169109902143563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486488020551289551257/100000000000000000000)
  centralHi := (243244010275644775629/50000000000000000000)
  directionLo := (489041780987995950669/100000000000000000000)
  directionHi := (48904178098799595067/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree097.table
  base := (128685966368982175650748245353679287951/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-19442156528134578096491244184890618375000000000)
      constant := (505768181579387961211863755526789870651951854140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree097.table
  base := (10294877295305643767651069161040828725631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-8643215853022663509762505212939550875000000000)
      constant := (224901884371442011558792249564998781344831761163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489041780987995950669/100000000000000000000)
  centralHi := (48904178098799595067/10000000000000000000)
  directionLo := (491582274867503812609/100000000000000000000)
  directionHi := (49158227486750381261/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree098.table
  base := (2170049290063024186352596024415611865651/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-78569760619585320848749822345856308500000000000)
      constant := (2065791630020310099813327432892532777604170858035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree098.table
  base := (2712561609559251342969699429847222470021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2183063517593645682736166851341243812500000000)
      constant := (57412708233898348012935762718804480652576670633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491582274867503812609/100000000000000000000)
  centralHi := (49158227486750381261/10000000000000000000)
  directionLo := (494109706822188571601/100000000000000000000)
  directionHi := (247054853411094285801/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree099.table
  base := (5708261211432836158363523744582932898957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-4409494173701796072863037108452785750000000000)
      constant := (117164493764867735889382826831238635181413038561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree099.table
  base := (22833044825205525883476886999430180721179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-17642584575453003904253659195580799250000000000)
      constant := (468899690964231191245318783690290246009757056967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494109706822188571601/100000000000000000000)
  centralHi := (247054853411094285801/50000000000000000000)
  directionLo := (496624276277255919193/100000000000000000000)
  directionHi := (248312138138627959597/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree100.table
  base := (23987410430512393641045318887796794987123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-160344059267358675548639027116887957000000000000)
      constant := (4305160999061662631731373696089298447963851519511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree100.table
  base := (4797482082614623864539634836951007174209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-17820661010156842346617983580431648000000000000)
      constant := (478597844015676504243943839186696247823774705785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496624276277255919193/100000000000000000000)
  centralHi := (248312138138627959597/50000000000000000000)
  directionLo := (249563088817190316307/50000000000000000000)
  directionHi := (99825235526876126523/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree101.table
  base := (251635896349335422565625851771125853969/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-40486582070363173118552179582368906750000000000)
      constant := (1098325232642926416318742508061972137251053418325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree101.table
  base := (12581794810059064691957356099353124005499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-8999368722430340394491153982641248375000000000)
      constant := (244198062510095153791498379356129913367889934327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249563088817190316307/50000000000000000000)
  centralHi := (99825235526876126523/20000000000000000000)
  directionLo := (501615600447101686963/100000000000000000000)
  directionHi := (125403900111775421741/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree102.table
  base := (26361582442141162600675721307259341383459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-18172066366171856599975378838007033000000000000)
      constant := (498037952224982453750659139190050381015442891407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree102.table
  base := (26361582429556043200737503670562604163467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-18176813879564519231346632350133345500000000000)
      constant := (498294533973288232606425794672453284110915968791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501615600447101686963/100000000000000000000)
  centralHi := (125403900111775421741/25000000000000000000)
  directionLo := (504092729588421494253/100000000000000000000)
  directionHi := (252046364794210747127/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree103.table
  base := (13790694418980758349316587538421899357653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-82575433154820363162674050377325483500000000000)
      constant := (2286141458693495163155452844685133752553740024721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree103.table
  base := (27581388827271954136715119110929852929537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-18354890314268357673710956734984194250000000000)
      constant := (508293070871199157363450309296306689620180688901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504092729588421494253/100000000000000000000)
  centralHi := (252046364794210747127/50000000000000000000)
  directionLo := (506557745411028640723/100000000000000000000)
  directionHi := (126639436352757160181/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree104.table
  base := (2882300881047489023790404190787790488623/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-83376567661867371625458895983619318500000000000)
      constant := (2331562486314744380225846983953998779669759275055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree104.table
  base := (14411504400698109417331429947086408561103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-9266483374486098058037640559917521500000000000)
      constant := (259195867855375916814700597548956608034495571819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506557745411028640723/100000000000000000000)
  centralHi := (126639436352757160181/25000000000000000000)
  directionLo := (127252705975134272587/25000000000000000000)
  directionHi := (509010823900537090349/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree105.table
  base := (30086442349657400462368207251737063518791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-18706156037536528908498609242202923000000000000)
      constant := (528318637303137154303321019338327386471505947843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree105.table
  base := (30086442341947563910778274125179489286107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-18711043183676034558439605504685891750000000000)
      constant := (528590528489279534650507799597100103089474565511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127252705975134272587/25000000000000000000)
  centralHi := (509010823900537090349/100000000000000000000)
  directionLo := (20458085472884412747/4000000000000000000)
  directionHi := (127863034205527579669/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree106.table
  base := (980365295221241335943577706109302316289/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3569013009307554642624699116133750000000000)
      linear := (-400843569226232964863342392434938625000000000)
      constant := (11432809449676788725520742406231774122150862564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree106.table
  base := (31371689440532919730513571325702556382821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3172456008273381904555288103230000000000000)
      linear := (-356398483365657981147243960179938500000000000)
      constant := (10167725456689431298741492188083444930475800661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20458085472884412747/4000000000000000000)
  centralHi := (127863034205527579669/25000000000000000000)
  directionLo := (32117615741301005227/6250000000000000000)
  directionHi := (513881851860816083633/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree107.table
  base := (32678750095653690143902143598108965674399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-171559942366016794027626865605001647000000000000)
      constant := (4941055385416616951649631779565946789175135836243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree107.table
  base := (6535750018018992727767265526781964353789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-19067196053083711443168254274387589250000000000)
      constant := (549288497854647280112062076431443357272411842485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32117615741301005227/6250000000000000000)
  centralHi := (513881851860816083633/100000000000000000000)
  directionLo := (516300132756036389041/100000000000000000000)
  directionHi := (258150066378018194521/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree108.table
  base := (34007624289419157961396582784794568479043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-19240245708901201217021839646398813000000000000)
      constant := (559500030219430941911117426422769813244251355439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree108.table
  base := (17003812142349894391426067828447963960923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-9622636243893774942766289329619219000000000000)
      constant := (279893837219008209395594206739888863937831680679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516300132756036389041/100000000000000000000)
  centralHi := (258150066378018194521/50000000000000000000)
  directionLo := (129676784857559381209/25000000000000000000)
  directionHi := (518707139430237524837/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree109.table
  base := (7071662404672946972211464219131762794313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-174764480394204827878766248030176987000000000000)
      constant := (5130845866325692820141837031074163268747024421705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree109.table
  base := (17679156009679160203050749063581958440373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-9711674461245694163948451522044643375000000000)
      constant := (285193489476657164400385271924988364187858525529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129676784857559381209/25000000000000000000)
  centralHi := (518707139430237524837/100000000000000000000)
  directionLo := (2605515140561933797/500000000000000000)
  directionHi := (521103028112386759401/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree110.table
  base := (18365406646638499362369154482355893457011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-88183374704149422402167969621382328500000000000)
      constant := (2613546084229464283413414724433701812603309999127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree110.table
  base := (36730813289876115488892158466662468311071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-19601425357195226770261227428940135500000000000)
      constant := (581086411399420368215908228275312653364823772283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2605515140561933797/500000000000000000)
  centralHi := (521103028112386759401/100000000000000000000)
  directionLo := (261743975728142603877/50000000000000000000)
  directionHi := (104697590291257041551/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree111.table
  base := (9531282023903417758973386408157814515983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-4943583845066468381386267512648675750000000000)
      constant := (147895532732390780740336771923244883527678726059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree111.table
  base := (4765641011590879295135136876839299096923/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2472437723987383151578193976723873031250000000)
      constant := (73985746471924055965313793153704674513676896179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261743975728142603877/50000000000000000000)
  centralHi := (104697590291257041551/20000000000000000000)
  directionLo := (131465514663517626953/25000000000000000000)
  directionHi := (525862058654070507813/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree112.table
  base := (39541256427396942777009005902360960035207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-179571287436486878655475321667939997000000000000)
      constant := (5422286896039951128099993580296641786979377238299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree112.table
  base := (39541256424946990071369685847989943866101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-19957578226602903654989876198641833000000000000)
      constant := (602785660080438643317537587997829178272537802473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131465514663517626953/25000000000000000000)
  centralHi := (525862058654070507813/100000000000000000000)
  directionLo := (33014093471570507299/6250000000000000000)
  directionHi := (105645099109025623357/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree113.table
  base := (8195839657224749974334009243299967192813/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-181173556450580895581045012880527667000000000000)
      constant := (5521235321474558870924047455978427952066244244205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree113.table
  base := (8195839656808916885483491786457836372157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-20135654661306742097354200583492681750000000000)
      constant := (613785476313893320671747775645094699358729010805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33014093471570507299/6250000000000000000)
  centralHi := (105645099109025623357/20000000000000000000)
  directionLo := (530578404720636209991/100000000000000000000)
  directionHi := (66322300590079526249/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree114.table
  base := (42438953669690305033146148866713999508113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-20308425051630545834068300454790593000000000000)
      constant := (624564939407203628741940726979219566390581074549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree114.table
  base := (21219476833962973429603318013182429113479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-10156865548005290269859262484171765250000000000)
      constant := (312442710237598527051668774152692604117910524867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530578404720636209991/100000000000000000000)
  centralHi := (66322300590079526249/12500000000000000000)
  directionLo := (106584185124791250099/20000000000000000000)
  directionHi := (4163444731437158207/781250000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree115.table
  base := (43920522576328620842626554442372286196457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-184378094478768929432184395305703007000000000000)
      constant := (5721834295606521264836437497584137182379694054549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree115.table
  base := (274503266092696992837655145875337097467/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2561475941339302372760356169149297406250000000)
      constant := (79510686570484967135723749699075184465073203320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106584185124791250099/20000000000000000000)
  centralHi := (4163444731437158207/781250000000000000)
  directionLo := (535253194647069231883/100000000000000000000)
  directionHi := (133813298661767307971/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree116.table
  base := (45423905004553118823778008862763452302199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-185980363492862946357754086518290677000000000000)
      constant := (5823484844296052531276643859859358420577418720843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree116.table
  base := (4542390500328288548902781689343633400603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-10334941982709128712223586869022614000000000000)
      constant := (323692846289773188534462034498408157145196526595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535253194647069231883/100000000000000000000)
  centralHi := (133813298661767307971/25000000000000000000)
  directionLo := (268787672611623157899/50000000000000000000)
  directionHi := (537575345223246315799/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree117.table
  base := (23474550476557861009466662238879709929291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-10421257361497609071295765429493241500000000000)
      constant := (329224227818356965878499349439122821740938464343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree117.table
  base := (1173727523800951433262858571787921869143/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2605995050015261983351437265362009593750000000)
      constant := (82348252565233143501221186511132002133464901195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268787672611623157899/50000000000000000000)
  centralHi := (537575345223246315799/100000000000000000000)
  directionLo := (539887507916132032829/100000000000000000000)
  directionHi := (53988750791613203283/10000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree118.table
  base := (48496110420968083199324442870009703506443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-189184901521050980208893468943466017000000000000)
      constant := (6029488064907119017778105951474845263634342060751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree118.table
  base := (6062013802506732468301379029786889851437/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2628254604353241788646977813468365687500000000)
      constant := (83785809548819667726543916080483154843371727601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539887507916132032829/100000000000000000000)
  centralHi := (53988750791613203283/10000000000000000000)
  directionLo := (27109490525270416879/5000000000000000000)
  directionHi := (542189810505408337581/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree119.table
  base := (25032466703614907502402372589857639310331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-95393585267572498567231580078026843500000000000)
      constant := (3066920368412008242791222385582800037107131578367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree119.table
  base := (10012986681290860023260569853876394236517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-21204113269529772751540146892597774250000000000)
      constant := (681887060185388916900295432321651771660202282205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27109490525270416879/5000000000000000000)
  centralHi := (542189810505408337581/100000000000000000000)
  directionLo := (544482378069198557417/100000000000000000000)
  directionHi := (272241189034599278709/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree120.table
  base := (51655569911161768439009706488465634880163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-21376604394359890451114761263182373000000000000)
      constant := (693232679608815607036972606225804089067837789199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree120.table
  base := (51655569910503962935068282346765536613057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-21382189704233611193904471277448623000000000000)
      constant := (693587771906163390106851973498896523713520277861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544482378069198557417/100000000000000000000)
  centralHi := (272241189034599278709/50000000000000000000)
  directionLo := (273382666531680802487/50000000000000000000)
  directionHi := (21870613322534464199/4000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree121.table
  base := (26634009966071778826456194622140008721569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-96995854281666515492801271290614513500000000000)
      constant := (3172624101935799598946526670097788628951509789933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree121.table
  base := (26634009965792816892653692372370933384083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1586228004136690952277644051615000000000000)
      linear := (-203398737159787260719516940210372375000000000)
      constant := (6654609542950149607589442983104273527532912403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273382666531680802487/50000000000000000000)
  centralHi := (21870613322534464199/4000000000000000000)
  directionLo := (137259698849454673969/25000000000000000000)
  directionHi := (549038795397818695877/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree122.table
  base := (54902283469654656382372375823611413895439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-195593977577427047911172233793816697000000000000)
      constant := (6452302998999541054191221733475998109562175115523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree122.table
  base := (2196091338767259205445896537126063008439/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-21738342573641288078633120047150320500000000000)
      constant := (717289579124907970922411517077188543522591823675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137259698849454673969/25000000000000000000)
  centralHi := (549038795397818695877/100000000000000000000)
  directionLo := (551302882510047187287/100000000000000000000)
  directionHi := (68912860313755898411/12500000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree123.table
  base := (3534897532703656161845761054156597210383/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2738836758215570344954748958422282875000000000)
      constant := (91114701414751615059791196455980497217979314518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree123.table
  base := (28279180261428611863153859910415325151181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-10958209504172563260498722216000584625000000000)
      constant := (364645337311311850117371260690631852522085231313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551302882510047187287/100000000000000000000)
  centralHi := (68912860313755898411/12500000000000000000)
  directionLo := (276778854717934497493/50000000000000000000)
  directionHi := (553557709435868994987/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree124.table
  base := (58236251092589106011599584891215697187911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-198798515605615081762311616218992037000000000000)
      constant := (6669114712458444872640641732213683821183071710427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree124.table
  base := (1455906277306220727890458080948491972871/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2761811930381120620420221102106502250000000000)
      constant := (92673987255720723237602179358970984744964318415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276778854717934497493/50000000000000000000)
  centralHi := (553557709435868994987/100000000000000000000)
  directionLo := (555803388877654324311/100000000000000000000)
  directionHi := (69475423609706790539/12500000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree125.table
  base := (59935955177339841150018636978167594085129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-200400784619709098687881307431579707000000000000)
      constant := (6778871630787789491854633265095259485530555532853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree125.table
  base := (29967977588525654269787700766394063148833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-11136285938876401702863046600851433375000000000)
      constant := (376796624697126371712315238937151656014131909109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555803388877654324311/100000000000000000000)
  centralHi := (69475423609706790539/12500000000000000000)
  directionLo := (139510007817513783451/25000000000000000000)
  directionHi := (111608006254011026761/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree126.table
  base := (61657472777253948014479022754772455433251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-22444783737089235068161222071574153000000000000)
      constant := (765503250761059195281460906055193534235467969423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree126.table
  base := (30828736388504653372550359879988035919473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-11225324156228320924045208793276857750000000000)
      constant := (382947364334008174388575489561901337130088359829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139510007817513783451/25000000000000000000)
  centralHi := (111608006254011026761/20000000000000000000)
  directionLo := (560267744843376812117/100000000000000000000)
  directionHi := (280133872421688406059/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree127.table
  base := (2536032155684663863363356170570623301029/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-203605322647897132539020689856755047000000000000)
      constant := (7001087590643158098645628762431326535321309728825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree127.table
  base := (198127512162216196658871053628253670723/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-2828590593395060036306842746425570531250000000)
      constant := (97287041983374940363069796841150663206027730660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560267744843376812117/100000000000000000000)
  centralHi := (280133872421688406059/50000000000000000000)
  directionLo := (562486635684690963251/100000000000000000000)
  directionHi := (140621658921172740813/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree128.table
  base := (4072871782609262004529691501711994818451/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-25650948957748893683073797633667839625000000000)
      constant := (889193329021029208661421741568968570249340162414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree128.table
  base := (65165948521572351867091623303068199556417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-22806801181864318732819066356255413000000000000)
      constant := (790798070991154552655278606240257944080086599141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562486635684690963251/100000000000000000000)
  centralHi := (140621658921172740813/25000000000000000000)
  directionLo := (564696807796786938973/100000000000000000000)
  directionHi := (282348403898393469487/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree129.table
  base := (33476453332999374019548995532994605796691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-11489436704226953688342226237885021500000000000)
      constant := (401494798968022156584713512866882833814519324543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree129.table
  base := (66952906665849684078740726168195273009411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-22984877616568157175183390741106261750000000000)
      constant := (803399934040441594660055798041392379199180865103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564696807796786938973/100000000000000000000)
  centralHi := (282348403898393469487/50000000000000000000)
  directionLo := (113379672631010961677/20000000000000000000)
  directionHi := (283449181577527404193/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree130.table
  base := (2148802447648223572317436302788409004329/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-26051516211272397914466220436814757125000000000)
      constant := (917645854801419088976435696021738332935889309012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree130.table
  base := (34380839162308398387272472226139212861397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-11581477025635997808773857562978555250000000000)
      constant := (408050962507413708597702845686938277152193020681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113379672631010961677/20000000000000000000)
  centralHi := (283449181577527404193/50000000000000000000)
  directionLo := (569091401762387792987/100000000000000000000)
  directionHi := (142272850440596948247/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree131.table
  base := (35296131748938598779121287428079463789409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-105007199352136600120649727353552863500000000000)
      constant := (3728164001564422381118261738725982809711069936813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree131.table
  base := (35296131748885046976448402302034920239803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-11670515242987917029956019755403979625000000000)
      constant := (414452021957142171103395406353301468163197636919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569091401762387792987/100000000000000000000)
  centralHi := (142272850440596948247/25000000000000000000)
  directionLo := (22851040868087512093/4000000000000000000)
  directionHi := (285638010851093901163/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree132.table
  base := (14488932437062842972979543926770111280507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-23512963079818579685207682879965933000000000000)
      constant := (841376652841851842655733597979502100705734483555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree132.table
  base := (18111165546305859152635559027348070204771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-5879776730169918125569090973914702000000000000)
      constant := (210451572684697338919573690564521812617069282383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22851040868087512093/4000000000000000000)
  centralHi := (285638010851093901163/50000000000000000000)
  directionLo := (286726159594776781591/50000000000000000000)
  directionHi := (573452319189553563183/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree133.table
  base := (74318874386982279813428998361145101943047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-213218936732461234092438837132281067000000000000)
      constant := (7689352455754645225628356622507643328892867265179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree133.table
  base := (14863774877381068580474931830182961933211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-23697183355383510944640688280509656750000000000)
      constant := (854808665488323359590914879778793738278846412515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286726159594776781591/50000000000000000000)
  centralHi := (573452319189553563183/100000000000000000000)
  directionLo := (575620388620726928027/100000000000000000000)
  directionHi := (143905097155181732007/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree134.table
  base := (76214900102821836359950010216104138719233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-214821205746555251018008528344868737000000000000)
      constant := (7807215743662637481514566847227141092486302744781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree134.table
  base := (76214900102756634015291183265487667102019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-23875259790087349387005012665360505500000000000)
      constant := (867911168162870542963618026715011288951397722287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575620388620726928027/100000000000000000000)
  centralHi := (143905097155181732007/25000000000000000000)
  directionLo := (288890161310434630551/50000000000000000000)
  directionHi := (577780322620869261103/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree135.table
  base := (78132739332783709396722350007558752909713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-24047052751183251993730913284161823000000000000)
      constant := (880664415477836123023410546622527849691146751349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree135.table
  base := (78132739332728454905054430228723835474503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-24053336224791187829369337050211354250000000000)
      constant := (881113798762417853047670170014395749818666890019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288890161310434630551/50000000000000000000)
  centralHi := (577780322620869261103/100000000000000000000)
  directionLo := (115986442418047263853/20000000000000000000)
  directionHi := (289966106045118159633/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree136.table
  base := (80072392076827432116452605889071374062443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-218025743774743284869147910770044077000000000000)
      constant := (8045644442668210797971995815125237608001465752751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree136.table
  base := (20018098019195152576001952627625623273769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-6057853164873756567933415358765550750000000000)
      constant := (223604139321738637688206423920604037646922685037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115986442418047263853/20000000000000000000)
  centralHi := (289966106045118159633/50000000000000000000)
  directionLo := (18189879570275523639/3125000000000000000)
  directionHi := (582076146248816756449/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree137.table
  base := (41016929167459919914335786657362337039871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-109814006394418650897358800991315873500000000000)
      constant := (4083104926882807403704924487359642321065581092147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree137.table
  base := (20508464583720041469337220562978067354983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-6102372273549716178524496454978262937500000000)
      constant := (226954860934117959228513107730075390914042248059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18189879570275523639/3125000000000000000)
  centralHi := (582076146248816756449/100000000000000000000)
  directionLo := (11684244253589925467/2000000000000000000)
  directionHi := (584212212679496273351/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree138.table
  base := (42008569053516943937482412656001668046441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-12290571211273962151127071844178856500000000000)
      constant := (460426442921815116950086187728174513156971781293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree138.table
  base := (21004284526750068092690836166566296238189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-6146891382225675789115577551190975125000000000)
      constant := (230330614527740634533881865260992550369533169697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11684244253589925467/2000000000000000000)
  centralHi := (584212212679496273351/100000000000000000000)
  directionLo := (586340497369806496597/100000000000000000000)
  directionHi := (293170248684903248299/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree139.table
  base := (43011115696573829009331129223578813596689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14276052037230218570498796464535000000000000)
      linear := (-2102193875632314487225065890639689500000000000)
      constant := (79340026407069150824506512022513777694068183241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree139.table
  base := (86022231393119177291671961879436191351387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-24765641963606541598826634589614749250000000000)
      constant := (934925600410420842738550913867224452512861618951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586340497369806496597/100000000000000000000)
  centralHi := (293170248684903248299/50000000000000000000)
  directionLo := (588461084752314893503/100000000000000000000)
  directionHi := (9194704449254920211/1562500000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree140.table
  base := (88049138193243523344507041264374531182203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-224434819831119352571426675620394757000000000000)
      constant := (8533310333435546069375796439682346859575884499071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree140.table
  base := (1100614227415242428765715515471537560543/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-3117964799788797505148869871808199750000000000)
      constant := (118578608829355259855690237928162089562254549390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588461084752314893503/100000000000000000000)
  centralHi := (9194704449254920211/1562500000000000000)
  directionLo := (590574057743709400179/100000000000000000000)
  directionHi := (29528702887185470009/5000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree141.table
  base := (90097858507307446464618959767723499860839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-25115232093912596610777374092553603000000000000)
      constant := (961942063939031844148508976807709748628319938147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree141.table
  base := (90097858507287005233970116815120458382477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-25121794833014218483555283359316446750000000000)
      constant := (962432268784222527898396189127538414938359027521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590574057743709400179/100000000000000000000)
  centralHi := (29528702887185470009/5000000000000000000)
  directionLo := (148169874445657238211/25000000000000000000)
  directionHi := (118535899556525790569/20000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree142.table
  base := (92168392335328389831574309064624392044137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4770000000000000000000000000000000000000000
      center := (83952)
      previous := (41976)
      next := (41976)
      square := (300190739128427527965259358310000000000000)
      linear := (-45157579420612455152264641548417000000000000)
      constant := (1742223274190939303881793855898074835005053349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree142.table
  base := (23042098083827768411910876305969204040503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132500000000000000000000000000000000000000
      center := (2332)
      previous := (1166)
      next := (1166)
      square := (8338631642456320221257204397500000000000)
      linear := (-1254704982529163703923805184693875000000000)
      constant := (48419747810878757586545857211068922501646659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148169874445657238211/25000000000000000000)
  centralHi := (118535899556525790569/20000000000000000000)
  directionLo := (594777484866288756463/100000000000000000000)
  directionHi := (37173592804143047279/6250000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree143.table
  base := (94260739677297820327784443978490766679503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-229241626873401403348135749258157767000000000000)
      constant := (8908517182671240851602792948740892213454565695171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree143.table
  base := (94260739677283152160325611873827160992141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-25477947702421895368283932129018144250000000000)
      constant := (990339448857850042163287123638624600232190787393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594777484866288756463/100000000000000000000)
  centralHi := (37173592804143047279/6250000000000000000)
  directionLo := (298434048792973446641/50000000000000000000)
  directionHi := (596868097585946893283/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree144.table
  base := (48187450266604646566811238037684796878623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-12824660882638634459650302248374746500000000000)
      constant := (501965974881967697922469087931855436236452342779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree144.table
  base := (96374900533196868650142199846792715519947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-25656024137125733810648256513868993000000000000)
      constant := (1004443230782093148004008060131290377183610799831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298434048792973446641/50000000000000000000)
  centralHi := (596868097585946893283/100000000000000000000)
  directionLo := (598951413161256759137/100000000000000000000)
  directionHi := (299475706580628379569/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree145.table
  base := (98510874903058102259923539394426237713261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-232446164901589437199275131683333107000000000000)
      constant := (9163158620809046848053886427079525510877085730377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree145.table
  base := (1970217498060951575331222436788955960811/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-12917050285914786126506290449359920875000000000)
      constant := (509323570315643672326104374445259825909662682575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598951413161256759137/100000000000000000000)
  centralHi := (299475706580628379569/50000000000000000000)
  directionLo := (601027507473547810663/100000000000000000000)
  directionHi := (75128438434193476333/12500000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree146.table
  base := (100668662786840987135066642292045174852109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-234048433915683454124844822895920777000000000000)
      constant := (9291830401472117867720806224855677976506862660713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree146.table
  base := (100668662786832074196569733046876458274359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-26012177006533410695376905283570690500000000000)
      constant := (1032951178405431774933276662565848614955285317107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601027507473547810663/100000000000000000000)
  centralHi := (75128438434193476333/12500000000000000000)
  directionLo := (603096455098075205303/100000000000000000000)
  directionHi := (75387056887259400663/12500000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree147.table
  base := (20569652836911177264595121564286807656671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-26183411436641941227823834900945383000000000000)
      constant := (1046822543318291851640517328032356337310278805415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree147.table
  base := (51424132092274168903688743419884657360783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-13095126720618624568870614834210769625000000000)
      constant := (523677672052262949961896376221342395604021226459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603096455098075205303/100000000000000000000)
  centralHi := (75387056887259400663/12500000000000000000)
  directionLo := (151289582333819278077/25000000000000000000)
  directionHi := (605158329335277112309/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree148.table
  base := (21009935819240346173327939231274228767369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-237252971943871487975984205321096117000000000000)
      constant := (9551876085986570668817372735861792554510892502665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree148.table
  base := (5252483954809766909934838776140383688871/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-6592082468985271895026388513318097000000000000)
      constant := (265464909432142361015361994377561699812783658415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151289582333819278077/25000000000000000000)
  centralHi := (605158329335277112309/100000000000000000000)
  directionLo := (303606601120538380529/50000000000000000000)
  directionHi := (607213202241076761059/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree149.table
  base := (53636453760889135472351043664461422309041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-119427620478982752450776948266841893500000000000)
      constant := (4841624994918974639584632142307899953243160699837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree149.table
  base := (107272907521772857384805385320701681522849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-26546406310644926022469878438123236750000000000)
      constant := (1076464059277562349106342976747549122943441635877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303606601120538380529/50000000000000000000)
  centralHi := (607213202241076761059/100000000000000000000)
  directionLo := (609261144656264667799/100000000000000000000)
  directionHi := (3046305723281323339/500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree150.table
  base := (27379487365321482633022026394303999014237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-6679375277001653384086766326285318250000000000)
      constant := (272653461150521208758116808650757963578630742001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree150.table
  base := (109517949461281346325091897172683472495329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-26724482745348764464834202822974085500000000000)
      constant := (1091168608751504735542650475489869229365744534917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609261144656264667799/100000000000000000000)
  centralHi := (3046305723281323339/500000000000000000)
  directionLo := (19103194569843591823/3125000000000000000)
  directionHi := (611302226234994938337/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree151.table
  base := (13973100614340710699956376103438644363703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-30257472373269192344086659869857390875000000000)
      constant := (1243587490091126965495467776701955424750252594571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree151.table
  base := (111784804914721803861606496021286089022403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-26902559180052602907198527207824934250000000000)
      constant := (1105973286150396870233997547798858499035819976719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19103194569843591823/3125000000000000000)
  centralHi := (611302226234994938337/100000000000000000000)
  directionLo := (306668257736214038851/50000000000000000000)
  directionHi := (613336515472428077703/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree152.table
  base := (28518368470524740524431284166065199771431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-60915512000061888919565742542861699250000000000)
      constant := (2520693986942177333490683419942264189566792811067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree152.table
  base := (14259184235261959416062079366370047741351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-3385079451844555168695356449084472875000000000)
      constant := (140109761434279892416830546394013182390199970723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306668257736214038851/50000000000000000000)
  centralHi := (613336515472428077703/100000000000000000000)
  directionLo := (615364079731551344023/100000000000000000000)
  directionHi := (76920509966443918003/12500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree153.table
  base := (29095989090851887641398838664354743617457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-6812897694842821461217573927334290750000000000)
      constant := (283826463403829129187304186344105675916506839061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree153.table
  base := (4655358254536190707692259268545384436229/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-27258712049460279791927175977526631750000000000)
      constant := (1135883024723032025617263450496426418547952765425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615364079731551344023/100000000000000000000)
  centralHi := (76920509966443918003/12500000000000000000)
  directionLo := (617384985269206358709/100000000000000000000)
  directionHi := (61738498526920635871/10000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree154.table
  base := (59358126179326767355567781516634408938907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-123433293014217794764701176298311068500000000000)
      constant := (5176815062518219342349373720689150815954911399199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree154.table
  base := (14839531544831397322724774384421140857923/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-3429598560520514779286437545297185062500000000)
      constant := (143873510737097011188953007257474454931277611679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617384985269206358709/100000000000000000000)
  centralHi := (61738498526920635871/10000000000000000000)
  directionLo := (309699648630676212393/50000000000000000000)
  directionHi := (619399297261352424787/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree155.table
  base := (24214072373567846345461784101225858613221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-248468855042529606454972043809209807000000000000)
      constant := (10490408275264485007652683792769175319547154240485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree155.table
  base := (12107036186783723698621485740734616568147/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-13807432459433978338327912373614164625000000000)
      constant := (583096637497735976630384617946956226667276442155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309699648630676212393/50000000000000000000)
  centralHi := (619399297261352424787/100000000000000000000)
  directionLo := (155351769956898201557/25000000000000000000)
  directionHi := (621407079827592806229/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree156.table
  base := (123446284890967142467535698313008278841901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-27785680450735958153393526113533053000000000000)
      constant := (1180898570357999292561039716633919038883027215873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree156.table
  base := (61723142445482726877184275007542291001233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-13896470676785897559510074566039589000000000000)
      constant := (590749296009560143847854327098708124576172424309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155351769956898201557/25000000000000000000)
  centralHi := (621407079827592806229/100000000000000000000)
  directionLo := (623408396054990080061/100000000000000000000)
  directionHi := (311704198027495040031/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree157.table
  base := (31461005357009977475196227081847139975523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378315378986600792118218106310177500000000000)
      linear := (-62918348267679410076527856558596286750000000000)
      constant := (2691666674727242729014575908117513966858123658311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree157.table
  base := (125844021428038480324216772890492164271429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-27971017788275633561384473516930026750000000000)
      constant := (1196904036967721801209075732115645006465828000217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623408396054990080061/100000000000000000000)
  centralHi := (311704198027495040031/50000000000000000000)
  directionLo := (78175413502649448341/12500000000000000000)
  directionHi := (625403308021195586729/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree158.table
  base := (4008236608720633891206335988048958534053/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-31659457760601457153960139680871602125000000000)
      constant := (1363268371540677933799152899958213598468067518084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree158.table
  base := (128263571479059074362613896875293466010683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-28149094222979472003748797901780875500000000000)
      constant := (1212409609841277230574996952469494799413222209159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78175413502649448341/12500000000000000000)
  centralHi := (625403308021195586729/100000000000000000000)
  directionLo := (627391876816916969717/100000000000000000000)
  directionHi := (313695938408458484859/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree159.table
  base := (130704935044031095577699415040921975101561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3172456008273381904555288103230000000000000)
      linear := (-534335285322653404941825594674131000000000000)
      constant := (23158339525097186790698413895327986676486969001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree159.table
  base := (65352467522015035602600399682860705919673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1586228004136690952277644051615000000000000)
      linear := (-267237459034748211755784172515393625000000000)
      constant := (11585050100375352201118882032033484595884821593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627391876816916969717/100000000000000000000)
  centralHi := (313695938408458484859/50000000000000000000)
  directionLo := (314687081283873405011/50000000000000000000)
  directionHi := (629374162567746810023/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree160.table
  base := (66584056061477613619761112056733178733381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-128240100056499845541410249936074078500000000000)
      constant := (5593904821173390868749330807194041722055602417217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree160.table
  base := (66584056061477180081620678837628113469709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-14252623546193574444238723335741286500000000000)
      constant := (621860569681626440692923832393641580960042562657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314687081283873405011/50000000000000000000)
  centralHi := (629374162567746810023/100000000000000000000)
  directionLo := (63135022445537442193/10000000000000000000)
  directionHi := (631350224455374421931/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree161.table
  base := (27130620543167119763557190290699099765399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-258082469127093708008390191084735827000000000000)
      constant := (11329992038951701405056005811118341388172942616215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree161.table
  base := (135653102715834864912941585958984188827549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-28683323527090987330841771056333421750000000000)
      constant := (1259527096011674655904078450064553049705060248977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63135022445537442193/10000000000000000000)
  centralHi := (631350224455374421931/100000000000000000000)
  directionLo := (316660060369100990797/50000000000000000000)
  directionHi := (126664024147640396319/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree162.table
  base := (69079953411337574235350256321185572044457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-14426929896732651385219993460962416500000000000)
      constant := (637393063515895787044670376569044218339833710061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree162.table
  base := (17269988352834315913483040753653845507599/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-3607674995224353221650761930148033812500000000)
      constant := (159429147573131680357141974545360432799395497627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316660060369100990797/50000000000000000000)
  centralHi := (126664024147640396319/20000000000000000000)
  directionLo := (79410488596423163293/12500000000000000000)
  directionHi := (127056781754277061269/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree163.table
  base := (8793032777717301236275587877462112984483/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-32660875894410217732441196688738895875000000000)
      constant := (1452132369418757137594236592468223954648258978062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree163.table
  base := (14068852444347629406023797703519054326971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-14519738198249332107785209913017559625000000000)
      constant := (645719696541695014763482950884081083176467864915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79410488596423163293/12500000000000000000)
  centralHi := (127056781754277061269/20000000000000000000)
  directionLo := (637241645026318788741/100000000000000000000)
  directionHi := (318620822513159394371/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree164.table
  base := (71619477789121775375553066948003106937343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756630757973201584236436212620355000000000000)
      linear := (-131444638084687879392549632361249418500000000000)
      constant := (5880971737571753635752016605410275435807936672051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree164.table
  base := (71619477789121552912706512550967743682677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84070084219244620470715134735595000000000000)
      linear := (-14608776415601251328967372105442984000000000000)
      constant := (653772866753342600788640360854941506295431862121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637241645026318788741/100000000000000000000)
  centralHi := (318620822513159394371/50000000000000000000)
  directionLo := (639193385109583212711/100000000000000000000)
  directionHi := (79899173138697901589/12500000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree165.table
  base := (145811200226978264832102867372313977882871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-29387949464829975078963217326120723000000000000)
      constant := (1323080966962942412072777324201700412412900293683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree165.table
  base := (36452800056744472074526016904616139855213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-7348907316476585275074767148934204187500000000)
      constant := (330938050463734935168678559829064255267521197849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639193385109583212711/100000000000000000000)
  centralHi := (79899173138697901589/12500000000000000000)
  directionLo := (128227836756274887607/20000000000000000000)
  directionHi := (160284795945343609509/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree166.table
  base := (148405258389683863635033656040244600162287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-266093814197563792636238647147674177000000000000)
      constant := (12054414637918987389297346796066575432032428341859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree166.table
  base := (37101314597420886247901019244024065390639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-7393426425152544885665848245146916375000000000)
      constant := (335014699532038605639905869474997482489800693547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128227836756274887607/20000000000000000000)
  centralHi := (160284795945343609509/25000000000000000000)
  directionLo := (643079094973430231891/100000000000000000000)
  directionHi := (160769773743357557973/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree167.table
  base := (151021130066363221067274322293884637233763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1513261515946403168472872425240710000000000000)
      linear := (-267696083211657809561808338360261847000000000000)
      constant := (12202001280901031223905183730942823620652905457991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree167.table
  base := (37755282516590737855938228598796889066957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42035042109622310235357567367797500000000000)
      linear := (-7437945533828504496256929341359628562500000000)
      constant := (339116380581582503873184066675727042498545477561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643079094973430231891/100000000000000000000)
  centralHi := (160769773743357557973/25000000000000000000)
  directionLo := (322506585903235925311/50000000000000000000)
  directionHi := (645013171806471850623/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree168.table
  base := (1920735190712739733101790525523904117103/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-3740254892024330923435805966289576625000000000)
      constant := (171534564327953056181578810534220720846787598190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree168.table
  base := (9603675953563684404854111021668034893529/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21017521054811155117678783683898750000000000)
      linear := (-3741232321252232053424005218786170375000000000)
      constant := (171621546806183409876957892763968112023217647034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell174.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322506585903235925311/50000000000000000000)
  centralHi := (645013171806471850623/100000000000000000000)
  directionLo := (32347073330358816479/5000000000000000000)
  directionHi := (646941466607176329581/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree169.table
  base := (19539789245206817726481158412533576872609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189157689493300396059109053155088750000000000)
      linear := (-33862577654980730426618465098179648375000000000)
      constant := (1562484586256720074828660451650834396004070079213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree169.table
  base := (156318313961654348742410118510635332523143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168140168438489240941430269471190000000000000)
      linear := (-30107935004721694869756366135140211750000000000)
      constant := (1389579354497566962973225023462902384094643184739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell174.Kernel169
