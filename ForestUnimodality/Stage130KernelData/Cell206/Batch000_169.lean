import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell206.Parameters
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch000_049
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch050_099
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch100_149
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch150_199
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch000_049
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch050_099
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch100_149
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree000.table
  base := (175885677232615809419939979/2000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77098584847481652082556991250000000000)
      linear := (-5634355232359811692377515875000000000)
      constant := (109928548270384880887462486875000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree000.table
  base := (175885677232615809419939979/2000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77098584847481652082556991250000000000)
      linear := (-5634355232359811692377515875000000000)
      constant := (109928548270384880887462486875000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree001.table
  base := (489611708274334604468532283896591153615937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-40498590600436588067002306865283370500000000000)
      constant := (28269121440115654302439544873118490353103266936233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree001.table
  base := (122377890392221150243015406918088790334571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-91143793274073060079912859901732318000000000000)
      constant := (63592530943167460479959087416380667131005847801851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49894679346064433991/100000000000000000000)
  directionHi := (6236834918258054249/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree002.table
  base := (144182762271975436687207378713073677884083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-39197856671109771238294874330828399000000000000)
      constant := (8342980269111155682477529126270157573973720851947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree002.table
  base := (72065595082671181577498189799144192536531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-176434283866175444430642273398417264250000000000)
      constant := (37530065547288416103301159704445873013252878176611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49894679346064433991/100000000000000000000)
  centralHi := (6236834918258054249/12500000000000000000)
  directionLo := (35280866110730535851/50000000000000000000)
  directionHi := (70561732221461071703/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree003.table
  base := (181742343911664141033247744493389660075513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-116292836084002496886177190458030225500000000000)
      constant := (10584082935969952443708832312635022304000378166817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree003.table
  base := (45415183134320385756384034712256721905761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-29080530495364203197930187432789134500000000000)
      constant := (2644855156603499380858947899175494218787099810249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/50000000000000000000)
  centralHi := (70561732221461071703/100000000000000000000)
  directionLo := (21605029913685271329/25000000000000000000)
  directionHi := (86420119654741085317/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree004.table
  base := (24611039097120170045156100291918729565391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-154189958825785451295764632254403653000000000000)
      constant := (7268977700333892281064126961483122481486842094595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree004.table
  base := (960904241001210572861826939338563014791/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-173507632525190106566050550195893578375000000000)
      constant := (8173834880128707630325642492511776685965598586736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21605029913685271329/25000000000000000000)
  centralHi := (86420119654741085317/100000000000000000000)
  directionLo := (49894679346064433991/50000000000000000000)
  directionHi := (99789358692128867983/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree005.table
  base := (89023460330492935292732020691803944928711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-192087081567568405705352074050777080500000000000)
      constant := (5397017668310925210922343478624107341210352496799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree005.table
  base := (8898086313675122378516729447970475215309/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-864611511284965194965661027776944206000000000000)
      constant := (24276109067048880512412830446613661277219300932145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49894679346064433991/50000000000000000000)
  centralHi := (99789358692128867983/100000000000000000000)
  directionLo := (111567894733354828469/100000000000000000000)
  directionHi := (11156789473335482847/10000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree006.table
  base := (3398633484284441370623737056509998642103/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-57496051077337840028734878961787627000000000000)
      constant := (1073604443747770870955105189844754636692635810635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree006.table
  base := (67941574432640537558700762280587390869381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-230042776104259991926026634393403133000000000000)
      constant := (4292812361365718829081135985985388039878320610829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111567894733354828469/100000000000000000000)
  centralHi := (11156789473335482847/10000000000000000000)
  directionLo := (122216505277640519213/100000000000000000000)
  directionHi := (61108252638820259607/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree007.table
  base := (26997726947169094053340252007520694941361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-133940663525567157262263478821761967750000000000)
      constant := (1810118835942358506515844906435634642200564770649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree007.table
  base := (13492971293454921220296905151971232821519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-602886736826687366184289340881841995500000000000)
      constant := (8143052770642691845932840048212167892127094105439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122216505277640519213/100000000000000000000)
  centralHi := (61108252638820259607/50000000000000000000)
  directionLo := (5280356531799893029/4000000000000000000)
  directionHi := (66004456647498662863/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree008.table
  base := (44059435886434639390236255129076741359187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-305778449792917268934114399439897363000000000000)
      constant := (3199465508531256066914739916767234242191334425483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree008.table
  base := (44040778144017071990798175191654874029227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-2752708909675159002140075017514107767000000000000)
      constant := (28788517319182192833760281779204099845096565286587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5280356531799893029/4000000000000000000)
  centralHi := (66004456647498662863/50000000000000000000)
  directionLo := (35280866110730535851/25000000000000000000)
  directionHi := (28224692888584428681/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree009.table
  base := (7314654483840171336404045837619772743301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-343675572534700223343701841236270790500000000000)
      constant := (2940257850157663838668955830652179942000879620545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree009.table
  base := (36557907519944969714587248293095041551497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-343763430227063171060332519055649728000000000000)
      constant := (2939795237606190919588853458842273420350092420273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/25000000000000000000)
  centralHi := (28224692888584428681/20000000000000000000)
  directionLo := (74842019019096650987/50000000000000000000)
  directionHi := (5987361521527732079/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree010.table
  base := (7668559944731484803810895097373714494563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-95393173819120794438322320758161054500000000000)
      constant := (698205776874207623420368122809043065907187258267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree010.table
  base := (7665299138009345849071929253007885110557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-858758208602994519236477581371896834250000000000)
      constant := (6283335572341690554649255486288158520961272242317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74842019019096650987/50000000000000000000)
  centralHi := (5987361521527732079/4000000000000000000)
  directionLo := (15778082985732420131/10000000000000000000)
  directionHi := (157780829857324201311/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree011.table
  base := (1617071619346971628955450133833944540979/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-52433727252283266520359590603627205687500000000)
      constant := (341115981268231751981494474182306403209164782822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree011.table
  base := (5172368947140615433725328072519677010687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-3776194796780387614348827979474327122000000000000)
      constant := (24560175281742859978718962149700425313295910004235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15778082985732420131/10000000000000000000)
  centralHi := (157780829857324201311/100000000000000000000)
  directionLo := (1292827581453053533/781250000000000000)
  directionHi := (6619277217039634089/4000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree012.table
  base := (10938206399095515689069927673908913768051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-228683470380024543286232083312695536500000000000)
      constant := (1365814198297793628035066623772868200955026546859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree012.table
  base := (21866500552205232383665755231322108795189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-457484084349866350194638403717896323000000000000)
      constant := (2731808958865075591490230936277582768748035178301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1292827581453053533/781250000000000000)
  centralHi := (6619277217039634089/4000000000000000000)
  directionLo := (172840239309482170633/100000000000000000000)
  directionHi := (86420119654741085317/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree013.table
  base := (18496173921788863311167677896546125205911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-495264063501832040982051608421764500500000000000)
      constant := (2790082141496995319511424044294935584780406671599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree013.table
  base := (9243712254256786212296006688947338354473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-2229259360758603344577331643723903346000000000000)
      constant := (12557070434259702473131704945722639479950475313113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172840239309482170633/100000000000000000000)
  centralHi := (86420119654741085317/50000000000000000000)
  directionLo := (17989782475506938321/10000000000000000000)
  directionHi := (179897824755069383211/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree014.table
  base := (15604234383406011068614696528050506916557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-533161186243614995391639050218137928000000000000)
      constant := (2896890392136426134881401296815501285214499569813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree014.table
  base := (7798245829536936479881182227579872841529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-2399840341942808113278790470717273238500000000000)
      constant := (13038602049173330367242584348425584438595972022249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17989782475506938321/10000000000000000000)
  centralHi := (179897824755069383211/100000000000000000000)
  directionLo := (93344397767959598371/50000000000000000000)
  directionHi := (186688795535919196743/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree015.table
  base := (3277000634750601041726219074943848994443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-142764577246349487450306623003627838875000000000)
      constant := (761677319124942165475532485458622361219834529187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree015.table
  base := (6550574410899172647388870096216634079939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-285602369236334764664472144190071459000000000000)
      constant := (1523744191634447371808346684676515455330438141051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93344397767959598371/50000000000000000000)
  centralHi := (186688795535919196743/100000000000000000000)
  directionLo := (48310315542916680617/25000000000000000000)
  directionHi := (193241262171666722469/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree016.table
  base := (1367189809288907728963412661610511136743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-76119428965897613026351741726360597875000000000)
      constant := (404437637435178122481317349583443470695040429887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree016.table
  base := (2186291556673738926329230199510467811639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-5482004608622435301363416249408026047000000000000)
      constant := (29128386937905949002073686179011109029802069285795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48310315542916680617/25000000000000000000)
  centralHi := (193241262171666722469/100000000000000000000)
  directionLo := (39915743476851547193/20000000000000000000)
  directionHi := (99789358692128867983/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree017.table
  base := (180763208719533414276135240914777899841/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-323426277234481929310200687803629105250000000000)
      constant := (1730056699433957391560730716712524361655237724225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree017.table
  base := (564550617607183512977931339365135899101/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-727895821373855604845791737924345729000000000000)
      constant := (3893976650485687584760079342063100488105236233562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39915743476851547193/20000000000000000000)
  centralHi := (99789358692128867983/50000000000000000000)
  directionLo := (642878228437961139/312500000000000000)
  directionHi := (205721033100147564481/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree018.table
  base := (1841578831478567705776799954398116304571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-171187419302686703257497204350907909500000000000)
      constant := (929507267619660050685814492163868720950329263539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree018.table
  base := (7361600845751180584484629056616791301047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-684925392595472708463250173042389513000000000000)
      constant := (3719447210526480738448450744940988753416268686223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642878228437961139/312500000000000000)
  centralHi := (205721033100147564481/100000000000000000000)
  directionLo := (105842598332191607553/50000000000000000000)
  directionHi := (211685196664383215107/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree019.table
  base := (5886643078682854300173294724250550902411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-722646799952529767439576259200005065500000000000)
      constant := (4007208483322640602862463841516606732288317540099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree019.table
  base := (588249739468837995031927092679573167173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-3252745247863831956786084605684122701000000000000)
      constant := (18039834427847744186371060080601876342141655309065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105842598332191607553/50000000000000000000)
  centralHi := (211685196664383215107/100000000000000000000)
  directionLo := (108742932544930463027/50000000000000000000)
  directionHi := (43497173017972185211/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree020.table
  base := (228511714410043128433647092309143392763/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-190135980673578180462290925249094623250000000000)
      constant := (1081495787028344456111797557212940339797857110335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree020.table
  base := (1141648985399349806157956423646286221359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-1711663114524018362743771716338746296750000000000)
      constant := (9737682926454657363429732730806273775045200756479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108742932544930463027/50000000000000000000)
  centralHi := (43497173017972185211/20000000000000000000)
  directionLo := (223135789466709656939/100000000000000000000)
  directionHi := (11156789473335482847/5000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree021.table
  base := (3393295735402557491140369345199276127091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-798441045436095676258751142792751920500000000000)
      constant := (4672979853274265258744839351290951207684115954219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree021.table
  base := (1695054301414069540509813359415130219619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-399323023359137943798778028852318054000000000000)
      constant := (2337547628460650760013046498864920117470850790171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223135789466709656939/100000000000000000000)
  centralHi := (11156789473335482847/5000000000000000000)
  directionLo := (228646144878890020401/100000000000000000000)
  directionHi := (114323072439445010201/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree022.table
  base := (467233541494383251879083480572058247781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-836338168177878630668338584589125348000000000000)
      constant := (5047063950099016423650772919387394128796279882145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree022.table
  base := (36459073499641268529183141185961443753/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-941122047854111565722615271666058094625000000000)
      constant := (5680604556732392735224416466938256760130361862344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228646144878890020401/100000000000000000000)
  centralHi := (114323072439445010201/50000000000000000000)
  directionLo := (234026790336117189411/100000000000000000000)
  directionHi := (58506697584029297353/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree023.table
  base := (172820437573213399214648022848592726143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-109279411364957698134740753298187346937500000000)
      constant := (680911932637739432787477724838445871893698344487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree023.table
  base := (1380130333039006292240864603139037071669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-7870138345201302063183839827315204542000000000000)
      constant := (49049211822162035286191501150301576442659202807589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234026790336117189411/100000000000000000000)
  centralHi := (58506697584029297353/25000000000000000000)
  directionLo := (119643238026717939889/50000000000000000000)
  directionHi := (239286476053435879779/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree024.table
  base := (64870821077073295414205749042759702921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-114016551707680567435939183522734025375000000000)
      constant := (734111785851437685123323429989575914108101088689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree024.table
  base := (516845484082745317777051008772608068961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-912366700841079066731861942366882703000000000000)
      constant := (5875773875585537144161473945218821892088715359049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119643238026717939889/50000000000000000000)
  centralHi := (239286476053435879779/100000000000000000000)
  directionLo := (122216505277640519213/50000000000000000000)
  directionHi := (244433010555281038427/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree025.table
  base := (-132927529851396440278450004823267812639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-475014768201613746948550454989122815250000000000)
      constant := (3161606090322087293440405934941475214760442384649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree025.table
  base := (-133850773450306499841164827417555164373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-4276231134969060568994837567644342056000000000000)
      constant := (28468631812735424247353755344891002346857330044987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122216505277640519213/50000000000000000000)
  centralHi := (244433010555281038427/100000000000000000000)
  directionLo := (249473396730322169957/100000000000000000000)
  directionHi := (124736698365161084979/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree026.table
  base := (-98124399771682957023510066808419550163/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-493963329572505224153344175887309529000000000000)
      constant := (3398854969596123638185391384637534264628983006665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree026.table
  base := (-196569879827424920241236029001493241711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-8893624232306530675392592789275423897000000000000)
      constant := (61210257291370913553596661740482912326671996879045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249473396730322169957/100000000000000000000)
  centralHi := (124736698365161084979/50000000000000000000)
  directionLo := (63603485902509359423/25000000000000000000)
  directionHi := (254413943610037437693/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree027.table
  base := (-1634977344080570315672033441722686284927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1025823781886793402716275793570992485500000000000)
      constant := (7295938711803108839495720183647880504704282586857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree027.table
  base := (-12784152366476947975141428675255097201/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-128260919370485280733270978378641162250000000000)
      constant := (912457057327197770808140726298005281612282692656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63603485902509359423/25000000000000000000)
  centralHi := (254413943610037437693/100000000000000000000)
  directionLo := (259260358964223255949/100000000000000000000)
  directionHi := (5185207179284465119/2000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree028.table
  base := (-1116766607132758169507075705762747790667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-531860452314288178562931617683682956500000000000)
      constant := (3908762308935443913438331930993674759045598379197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree028.table
  base := (-1117371307384015726301385428626584728639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-4787974078521674875099214048624451733500000000000)
      constant := (35196926476651326551969915655871952441783572665841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259260358964223255949/100000000000000000000)
  centralHi := (5185207179284465119/2000000000000000000)
  directionLo := (5280356531799893029/2000000000000000000)
  directionHi := (264017826589994651451/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree029.table
  base := (-2782310751692610291897131755395429698833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1101618027370359311535450677163739340500000000000)
      constant := (8362156049023938295151567812656027243912055415303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree029.table
  base := (-1391679412204058801778198935863149686683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-4958555059705879643800672875617821626000000000000)
      constant := (37649144439727864161510401125265328767278499361877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5280356531799893029/2000000000000000000)
  centralHi := (264017826589994651451/100000000000000000000)
  directionLo := (134345535638843499697/50000000000000000000)
  directionHi := (53738214255537399879/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree030.table
  base := (-1642906055630159836522252821866643748203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-569757575056071132972519059480056384000000000000)
      constant := (4464786583026534368812947589880576641446419042973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree030.table
  base := (-3286719527665542666884319162648940090797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1139808009086685425000473711691375893000000000000)
      constant := (8934208754030395216333213597115112213183244806027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134345535638843499697/50000000000000000000)
  centralHi := (53738214255537399879/20000000000000000000)
  directionLo := (273284413773266009199/100000000000000000000)
  directionHi := (683211034433165023/250000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree031.table
  base := (-936948303359052809597844544070017749091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-294353068213481305088656390189121548875000000000)
      constant := (2379889799557060633828201032529572412562015147781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree031.table
  base := (-3748578165597015095000936382461876724213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-10599434044148578362407181059209122822000000000000)
      constant := (85720673025065400601526575352126772152355716433947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273284413773266009199/100000000000000000000)
  centralHi := (683211034433165023/250000000000000000)
  directionLo := (277801817557848698187/100000000000000000000)
  directionHi := (69450454389462174547/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree032.table
  base := (-4171388771705896445696938257519843948793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1215309395595708174764213002552859623000000000000)
      constant := (10131933227413253292924094611785781156723185741663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree032.table
  base := (-417206723401132016108977950084575771539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-5470298003258493949905049356597931303500000000000)
      constant := (45617522242266284057578271179098892671845841754705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277801817557848698187/100000000000000000000)
  centralHi := (69450454389462174547/25000000000000000000)
  directionLo := (35280866110730535851/12500000000000000000)
  directionHi := (282246928885844286809/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree033.table
  base := (-911843216056620939220787881804639675863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1253206518337491129173800444349233050500000000000)
      constant := (10766544198019376498386888680633512331779326950165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree033.table
  base := (-36478416413157755709336937303051095977/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1253528663209488604134779596353622488000000000000)
      constant := (10772181632277574422515440877402713920735645925875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/12500000000000000000)
  centralHi := (282246928885844286809/100000000000000000000)
  directionLo := (143311555616197111039/50000000000000000000)
  directionHi := (286623111232394222079/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree034.table
  base := (-4913461238345206070697501313138061233227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1291103641079274083583387886145606478000000000000)
      constant := (11423265940624574851297076575500504839393492532157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree034.table
  base := (-4913966964235048739052932698815918929177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-11622919931253806974615934021169342177000000000000)
      constant := (102863309028952407937826762912251094940895729297463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143311555616197111039/50000000000000000000)
  centralHi := (286623111232394222079/100000000000000000000)
  directionLo := (290933475075633088773/100000000000000000000)
  directionHi := (145466737537816544387/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree035.table
  base := (-2617975416371748812484629578781395538453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-664500381910528518996487663970989952750000000000)
      constant := (6050996517424119285606759183542571922318573330723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree035.table
  base := (-2618193503586579469588207327098161093997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-5982040946811108256009425837578040981000000000000)
      constant := (54487559761172199550220401332137739198196027275043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290933475075633088773/100000000000000000000)
  centralHi := (145466737537816544387/50000000000000000000)
  directionLo := (295180903763489769053/100000000000000000000)
  directionHi := (147590451881744884527/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree036.table
  base := (-1382052892251685352139967377414273640767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-341724471640709998100640692434588333250000000000)
      constant := (3200659341945764530984893724807573796908854288297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree036.table
  base := (-5528587517064173614834160794587123077881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1367249317332291783269085481015869083000000000000)
      constant := (12809363762840880704613913675493897885549837112671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295180903763489769053/100000000000000000000)
  centralHi := (147590451881744884527/50000000000000000000)
  directionLo := (74842019019096650987/25000000000000000000)
  directionHi := (299368076076386603949/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree037.table
  base := (-5791519905522426338344141699850287275361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1404795009304622946812150211534726760500000000000)
      constant := (13525125269387586493643766424442545203203569623351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree037.table
  base := (-2895921873713413962022513447783933439881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-6323202909179517793412343491564780766000000000000)
      constant := (60895054827047279465213402655132805933084879492039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74842019019096650987/25000000000000000000)
  centralHi := (299368076076386603949/100000000000000000000)
  directionLo := (60699497197497043561/20000000000000000000)
  directionHi := (151748742993742608903/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree038.table
  base := (-37668396181721251692905981651079428521/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-180336516505800737652717206666387523500000000000)
      constant := (1783674390853757042016350470406971556213929818220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree038.table
  base := (-6027222186923827025861779903084306664759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-12987567780727445124227604637116301317000000000000)
      constant := (128492072922058437809781716359837124324018058688121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60699497197497043561/20000000000000000000)
  centralHi := (151748742993742608903/50000000000000000000)
  directionLo := (307571460034526569769/100000000000000000000)
  directionHi := (30757146003452656977/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree039.table
  base := (-1558843774167469804876067123240908632357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-370147313697047213907831273781868403875000000000)
      constant := (3758848849174744458420002853334550949355829967987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree039.table
  base := (-3117807492582463891317936731606587338193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-740484985727547481201695682839057839000000000000)
      constant := (7521650014470686816560621097271760800706807877063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307571460034526569769/100000000000000000000)
  centralHi := (30757146003452656977/10000000000000000000)
  directionLo := (77898043161725572547/25000000000000000000)
  directionHi := (311592172646902290189/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree040.table
  base := (-6417562347037952423428434513962819430063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1518486377529971810040912536923847043000000000000)
      constant := (15823082947935393826517643339579229223620197122233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree040.table
  base := (-128355372990606057130252137683274863007/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-6834945852732132099516719972544890443500000000000)
      constant := (71241301955622993181866070944058329586823882230825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77898043161725572547/25000000000000000000)
  centralHi := (311592172646902290189/100000000000000000000)
  directionLo := (15778082985732420131/5000000000000000000)
  directionHi := (315561659714648402621/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree041.table
  base := (-3287065323019588294725544763750093189781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-778191750135877382225249989360110235250000000000)
      constant := (8316210839919146981153982179710868905372489745571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree041.table
  base := (-82178849715156839047721948459930697113/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-1751381708479084217054544699884565084000000000000)
      constant := (18721307417021608694316558830242908621086742890470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15778082985732420131/5000000000000000000)
  centralHi := (315561659714648402621/100000000000000000000)
  directionLo := (319481830639725334271/100000000000000000000)
  directionHi := (1247975900936427087/390625000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree042.table
  base := (-6705603665672871655832602380847585388101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1594280623013537718860087420516593898000000000000)
      constant := (17463381368987727642412360796723423473123715152691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree042.table
  base := (-6705756022157830444378531237830086104259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1594690625577898141537697250340362273000000000000)
      constant := (17472554982834289718781144799234335424073579432069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319481830639725334271/100000000000000000000)
  centralHi := (1247975900936427087/390625000000000000)
  directionLo := (16167723953602492947/5000000000000000000)
  directionHi := (323354479072049858941/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree043.table
  base := (-106444061257343854555620701199133782247/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-204022218219415084158709357789120915687500000000)
      constant := (2289492088347087759352122755294936094381843873816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree043.table
  base := (-3406275380304523176977631956197076776087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-7346688796284746405621096453525000121000000000000)
      constant := (82464991470696534169714344373166985266002121161753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16167723953602492947/5000000000000000000)
  centralHi := (323354479072049858941/100000000000000000000)
  directionLo := (40897661562697284119/12500000000000000000)
  directionHi := (327181292501578272953/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree044.table
  base := (-6894946692555485248240519966342834172673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1670074868497103627679262304109340753000000000000)
      constant := (19190066495734442186858767743469416396339173854743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree044.table
  base := (-6895059006463696936003877210385990594433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-15034539554937902348645110561036740027000000000000)
      constant := (172801233089800486291821281679196649701664666434127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40897661562697284119/12500000000000000000)
  centralHi := (327181292501578272953/100000000000000000000)
  directionLo := (1292827581453053533/390625000000000000)
  directionHi := (330963860851981704449/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree045.table
  base := (-6953491663542361270203405815024376504397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1707971991238886582088849745905714180500000000000)
      constant := (20085752978198490403455684343733321462736491243627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree045.table
  base := (-6953588034522477980384753903920022530829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1708411279700701320672003135002608868000000000000)
      constant := (20096287298119906285944762259315529410741519984939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1292827581453053533/390625000000000000)
  centralHi := (330963860851981704449/100000000000000000000)
  directionLo := (10459490131252015169/3125000000000000000)
  directionHi := (334703684200064485409/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree046.table
  base := (-6988312634249539027679243971438720116781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1745869113980669536498437187702087608000000000000)
      constant := (21002981275346943948623781375310071521118573602571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree046.table
  base := (-1747098823132940513698109437659716232187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-3929215869918680355862736467252554899250000000000)
      constant := (47281476748807076678182174235197617600214584657653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10459490131252015169/3125000000000000000)
  centralHi := (334703684200064485409/100000000000000000000)
  directionLo := (16920108986361692867/5000000000000000000)
  directionHi := (338402179727233857341/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree047.table
  base := (-6999625649242257024092165430105653474453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1783766236722452490908024629498461035500000000000)
      constant := (21941738918295402420193890641512374741444398506723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree047.table
  base := (-1749924129732863550295344750778058271259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-4014506360510782740213465880749239845500000000000)
      constant := (49394771241324729348971524947206527541829276161621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16920108986361692867/5000000000000000000)
  centralHi := (338402179727233857341/100000000000000000000)
  directionLo := (171030343997190798403/50000000000000000000)
  directionHi := (342060687994381596807/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree048.table
  base := (-3493805895046555108221883458737490122763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-910831679732117722658806035647417231500000000000)
      constant := (11451007728013961354813142287608423018421396007933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree048.table
  base := (-6987672530120949680319529064628402452501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1822131933823504499806309019664855463000000000000)
      constant := (22914002852431814574897940007279239191839754213091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171030343997190798403/50000000000000000000)
  centralHi := (342060687994381596807/100000000000000000000)
  directionLo := (172840239309482170633/50000000000000000000)
  directionHi := (345680478618964341267/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree049.table
  base := (-695242285716798960974979576967708206033/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-929780241103009199863599756545603945250000000000)
      constant := (11941901063738050716904031641612698042287400852515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree049.table
  base := (-6952474896966832537363344883113321119301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-16740349366779950035659698830970438952000000000000)
      constant := (215066650384583669403179469743300189251525918627019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172840239309482170633/50000000000000000000)
  centralHi := (345680478618964341267/100000000000000000000)
  directionLo := (349262755422451037939/100000000000000000000)
  directionHi := (17463137771122551897/5000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree050.table
  base := (-3447093061552457441703806537169372590319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-948728802473900677068393477443790659000000000000)
      constant := (12443545793587426708006219297103023851486439793529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree050.table
  base := (-1723557673411184479903525255987764806087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-4270377832287089893265654121239294684250000000000)
      constant := (56025223274323104645161259940949089636871202731753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349262755422451037939/100000000000000000000)
  centralHi := (17463137771122551897/5000000000000000000)
  directionLo := (35280866110730535851/10000000000000000000)
  directionHi := (352808661107305358511/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree051.table
  base := (-6813008310694900136519646593791153883253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1935354727689584308546374396683954745500000000000)
      constant := (25911877675681368446999046459390664129231248107523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree051.table
  base := (-6813046471454631190003541971709671121667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1935852587946307678940614904327102058000000000000)
      constant := (25925410940456091951411053873845440746503622000197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/10000000000000000000)
  centralHi := (352808661107305358511/100000000000000000000)
  directionLo := (356319281515014325409/100000000000000000000)
  directionHi := (35631928151501432541/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree052.table
  base := (-1341795784507307761350518791620988082157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-1973251850431367262955961838480328173000000000000)
      constant := (26958155227406064742281675086078018195211326498935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree052.table
  base := (-6709011584917141256844543218371271737847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-17763835253885178647868451792930658307000000000000)
      constant := (242750020071630750167578469880745025750645817163193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356319281515014325409/100000000000000000000)
  centralHi := (35631928151501432541/10000000000000000000)
  directionLo := (17989782475506938321/5000000000000000000)
  directionHi := (359795649510138766421/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree053.table
  base := (-1316434605749451632449727371594099243733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2011148973173150217365549280276701600500000000000)
      constant := (28025919909721481426479013930019293156084264756015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree053.table
  base := (-3291100488187823074768741943102037749029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-9052498608126794092635684723458699046000000000000)
      constant := (126182409496296336076504073631722848514259408470251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17989782475506938321/5000000000000000000)
  centralHi := (359795649510138766421/100000000000000000000)
  directionLo := (363238748529764108319/100000000000000000000)
  directionHi := (2270242178311025677/625000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree054.table
  base := (-6432653601452554269982274112064517522083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2049046095914933171775136722073075028000000000000)
      constant := (29115168088228612020253805373823365327717835206053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree054.table
  base := (-6432677507772776773780846708113564127727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2049573242069110858074920788989348653000000000000)
      constant := (29130340286070198411926757004952653108484635681657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363238748529764108319/100000000000000000000)
  centralHi := (2270242178311025677/625000000000000000)
  directionLo := (9166237895823038941/2500000000000000000)
  directionHi := (366649515832921557641/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree055.table
  base := (-6260473470142780401280048834914019909843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2086943218656716126184724163869448455500000000000)
      constant := (30225896713904643013350221335622288690870427972213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree055.table
  base := (-39128086960272434698935733083949554021/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-2348415142623800907509650594361359707750000000000)
      constant := (34021840428233171098730938350680807248929969053980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9166237895823038941/2500000000000000000)
  centralHi := (366649515832921557641/100000000000000000000)
  directionLo := (185014422740203138461/50000000000000000000)
  directionHi := (370028845480406276923/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree056.table
  base := (-6065676959790628750710236224351867386671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2124840341398499080594311605665821883000000000000)
      constant := (31358103228559971534619840802223781418731908757561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree056.table
  base := (-1213138887435241083796902734164021131251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-19128483103358816797480122408877617447000000000000)
      constant := (282369778565068329320115710770269437912585169695345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185014422740203138461/50000000000000000000)
  centralHi := (370028845480406276923/100000000000000000000)
  directionLo := (93344397767959598371/25000000000000000000)
  directionHi := (74675518214367678697/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree057.table
  base := (-2924150631725696648009574685664623812983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1081368732070141017501949523731097655250000000000)
      constant := (16255892742809696193907888080827316233441984627953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree057.table
  base := (-584831620102426690426785454406468835783/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1081646948095957018604613336825797624000000000000)
      constant := (16264344928312918215878176270219461897016830513765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93344397767959598371/25000000000000000000)
  centralHi := (74675518214367678697/20000000000000000000)
  directionLo := (376696568263709514803/100000000000000000000)
  directionHi := (94174142065927378701/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree058.table
  base := (-224335103703297836427318355227789311039/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2200634586882064989413486489258568738000000000000)
      constant := (33686941683732089326567127451872833959296673476225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree058.table
  base := (-1402097589018532790065266981240007438451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-4952701757023908968071489429212774254250000000000)
      constant := (75834999419715750280976126387691595418307769935869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376696568263709514803/100000000000000000000)
  centralHi := (94174142065927378701/25000000000000000000)
  directionLo := (189993278544730465443/50000000000000000000)
  directionHi := (379986557089460930887/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree059.table
  base := (-5345932141235930422307824632088356787153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2238531709623847943823073931054942165500000000000)
      constant := (34883570311123823554680607270665450203779575812423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree059.table
  base := (-213837721771645192048913901202548479741/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-20151968990464045409688875370837836802000000000000)
      constant := (314115131893847036120954100502049431179402435184475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189993278544730465443/50000000000000000000)
  centralHi := (379986557089460930887/100000000000000000000)
  directionLo := (95812076025072623687/25000000000000000000)
  directionHi := (383248304100290494749/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree060.table
  base := (-5060986894365145474391319645441920944533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2276428832365630898232661372851315593000000000000)
      constant := (36101670098946008548346251498252772068861556124003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree060.table
  base := (-2530498102929582033526879378884058780609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1138507275157358608171766279156920921500000000000)
      constant := (18060199997677883776365494586732937195455890904919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95812076025072623687/25000000000000000000)
  centralHi := (383248304100290494749/100000000000000000000)
  directionLo := (386482524343333444937/100000000000000000000)
  directionHi := (193241262171666722469/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree061.table
  base := (-190142412221828647757968061980454834421/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2314325955107413852642248814647689020500000000000)
      constant := (37341239982161433166552795749403908748286228195275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree061.table
  base := (-2376784127945827145207503470183593766293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-10417146457600432242247355339405658186000000000000)
      constant := (168122696153285563591282893980683877939228338457467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386482524343333444937/100000000000000000000)
  centralHi := (193241262171666722469/50000000000000000000)
  directionLo := (389689903192066188383/100000000000000000000)
  directionHi := (12177809474752068387/3125000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree062.table
  base := (-2211833932642765517044336915786491466603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1176111538924598403525918128222031224000000000000)
      constant := (19301139533372294758695616780603985465008964617373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree062.table
  base := (-4423674651867532663283259249799237604181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-21175454877569274021897628332798056157000000000000)
      constant := (347600500909881342932215685714010998786217058903739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389689903192066188383/100000000000000000000)
  centralHi := (12177809474752068387/3125000000000000000)
  directionLo := (392871098042205831199/100000000000000000000)
  directionHi := (491088872552757289/125000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree063.table
  base := (-814264515529567349075137675005997039263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2390120200590979761461423698240435875500000000000)
      constant := (39884786602173652716031480605191904399397180797165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree063.table
  base := (-4071328369498875385702069645701869326839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2390735204437520395477838442976088438000000000000)
      constant := (39905435447573618970565808933306861332481259276849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392871098042205831199/100000000000000000000)
  centralHi := (491088872552757289/125000000000000000)
  directionLo := (15841069595399679087/4000000000000000000)
  directionHi := (49503342485623997147/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree064.table
  base := (-369653536002771004856623921652288095013/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1214008661666381357935505570018404651500000000000)
      constant := (20594380979178809045012723326161739081492944288415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree064.table
  base := (-3696540301854808471319481754070627761633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-21857778802306093096703463640771535727000000000000)
      constant := (370890641003231389354977567071695066218305226770927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15841069595399679087/4000000000000000000)
  centralHi := (49503342485623997147/12500000000000000000)
  directionLo := (399157434768515471931/100000000000000000000)
  directionHi := (99789358692128867983/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree065.table
  base := (-1649657689254986042884849289680498442809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1232957223037272835140299290916591365250000000000)
      constant := (21257102303140658671642792135686689203313483265119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree065.table
  base := (-1649659797078064330148831521821883475549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-11099470382337251317053190647379137756000000000000)
      constant := (191412831042394338833281635596627826347163911630131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399157434768515471931/100000000000000000000)
  centralHi := (99789358692128867983/25000000000000000000)
  directionLo := (100565941289169898857/25000000000000000000)
  directionHi := (402263765156679595429/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree066.table
  base := (-2879670329218666380665282904227596489013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2503811568816328624690186023629556158000000000000)
      constant := (43861114101767499713152469979884487022021139711683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree066.table
  base := (-359959240579858315701532766311665812541/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-313056982320040446826518040954791879125000000000)
      constant := (5485471920618482550925311171986515561323691396731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100565941289169898857/25000000000000000000)
  centralHi := (402263765156679595429/100000000000000000000)
  directionLo := (202673145597212053133/50000000000000000000)
  directionHi := (405346291194424106267/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree067.table
  base := (-2437606674379613351941038597680762255263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2541708691558111579099773465425929585500000000000)
      constant := (45229490071852621149621390624137730553799238815433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree067.table
  base := (-1218804870098968227666208263030825808217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-11440632344705660854456108301365877541000000000000)
      constant := (203637793126874509267018952168750919080208776511223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202673145597212053133/50000000000000000000)
  centralHi := (405346291194424106267/100000000000000000000)
  directionLo := (102101387971748898553/25000000000000000000)
  directionHi := (408405551886995594213/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree068.table
  base := (-9634423048848546973251591087814657/48828125000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-322450726787486816688670113402787876625000000000)
      constant := (5827416525419319559463259457090808568849506547200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree068.table
  base := (-394626490821997459085777505447195992597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-23222426651779731246315134256718494867000000000000)
      constant := (419790483180626939393998160380904521777104309642215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102101387971748898553/25000000000000000000)
  centralHi := (408405551886995594213/100000000000000000000)
  directionLo := (642878228437961139/156250000000000000)
  directionHi := (411442066200295128961/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree069.table
  base := (-1486244384119145517018745511944945247521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2617502937041677487918948349018676440500000000000)
      constant := (48030640233278741633984276407560805132283216769911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree069.table
  base := (-1486246611952467056787377317973745624791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2618176512683126753746450212300581628000000000000)
      constant := (48055407411561851385046080855595906440123851686481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642878228437961139/156250000000000000)
  centralHi := (411442066200295128961/100000000000000000000)
  directionLo := (414456334088664433567/100000000000000000000)
  directionHi := (12951760440270763549/3125000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree070.table
  base := (-9769541322766140554535337719162690417/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-663850014945865110582133947703762467000000000000)
      constant := (12365853485191610031190703508755547307287072036175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree070.table
  base := (-61059751927880262836984628908567330381/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-2988093822064568790140121195586496804625000000000)
      constant := (55675016855164049476413450788021126701201351123078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414456334088664433567/100000000000000000000)
  centralHi := (12951760440270763549/3125000000000000000)
  directionLo := (208724418727937302769/50000000000000000000)
  directionHi := (417448837455874605539/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree071.table
  base := (-445262298648152038303080027327075629311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7061613583350539477545559942570000000000000)
      linear := (-534278354002230390148407703354775500000000000)
      constant := (10100704848311193308988292072901723592370018361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree071.table
  base := (-89052783263768039053464742197671578201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030410000000000000000000000000000000000000000
      center := (18135216)
      previous := (9067608)
      next := (9067608)
      square := (63554522250154855297910039483130000000000000)
      linear := (-4809742618306875591851594369902542000000000000)
      constant := (90953161263112031779378078824985872489552953795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208724418727937302769/50000000000000000000)
  centralHi := (417448837455874605539/100000000000000000000)
  directionLo := (84084008210909595249/20000000000000000000)
  directionHi := (210210020527273988123/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree072.table
  base := (13603552211010126482988431967264040397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-341399288158378293893463834300974590375000000000)
      constant := (6549169709526737106234125020189565045313464980373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree072.table
  base := (435308158418575487592951159359111513/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1365948583402964966440378048481414111500000000000)
      constant := (26210162142435846747112838709967934355467236352125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84084008210909595249/20000000000000000000)
  centralHi := (210210020527273988123/50000000000000000000)
  directionLo := (105842598332191607553/25000000000000000000)
  directionHi := (423370393328766430213/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree073.table
  base := (685315749840833868209172662717477356879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2769091428008809305557298116204170150500000000000)
      constant := (53890527417565665430724378616607853740654403569511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree073.table
  base := (685314576066627354368292824757817434223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-24928236463621778933329722526652193792000000000000)
      constant := (485264231576448248547948213609705629867489691372863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105842598332191607553/25000000000000000000)
  centralHi := (423370393328766430213/100000000000000000000)
  directionLo := (426300327204191790837/100000000000000000000)
  directionHi := (213150163602095895419/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree074.table
  base := (642098896920884840537980773911747105963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1403494275375296129983442779000271789000000000000)
      constant := (27704581127252811948586627146080301401815614920867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree074.table
  base := (1284196794258278945321885174890974886289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-25269398425990188470732640180638933577000000000000)
      constant := (498938823978859107973911423434717121412964106543809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426300327204191790837/100000000000000000000)
  centralHi := (213150163602095895419/50000000000000000000)
  directionLo := (429210260829639966641/100000000000000000000)
  directionHi := (214605130414819983321/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree075.table
  base := (1905472950495007027270690465327660890251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2844885673492375214376472999796917005500000000000)
      constant := (56949262094737127077645930615469481684164500326659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree075.table
  base := (1905472099394593441131770802337050685081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2845617820928733112015061981625074818000000000000)
      constant := (56978521660299905912157476315660066845967495032129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429210260829639966641/100000000000000000000)
  centralHi := (214605130414819983321/50000000000000000000)
  directionLo := (432100598273705426583/100000000000000000000)
  directionHi := (54012574784213178323/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree076.table
  base := (2549139876554242224348216990459656052839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2882782796234158168786060441593290433000000000000)
      constant := (58510826860735508413675562516568044325432875657151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree076.table
  base := (509827830399823447474377973194894882713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-25951722350727007545538475488612413147000000000000)
      constant := (526867843772204557251707475377015382465780730022765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432100598273705426583/100000000000000000000)
  centralHi := (54012574784213178323/12500000000000000000)
  directionLo := (434971730179721852109/100000000000000000000)
  directionHi := (43497173017972185211/10000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree077.table
  base := (643039488745817984426740643683944208379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2920679918975941123195647883389663860500000000000)
      constant := (60093856487382155134394551179109974393159084165055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree077.table
  base := (20094980168766261563609610657569562391/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-3286610539136927135367674142824894116500000000000)
      constant := (67640283735372619907237301481741360979733209545420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434971730179721852109/100000000000000000000)
  centralHi := (43497173017972185211/10000000000000000000)
  directionLo := (8756480687641293227/2000000000000000000)
  directionHi := (437824034382064661351/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree078.table
  base := (1951822352131717534802281024316657985037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1479288520858862038802617662593018644000000000000)
      constant := (30849175459988941591748561571467294378649041298133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree078.table
  base := (3903644179400520686210827630632437942197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2959338475051536291149367866287321413000000000000)
      constant := (61729996976018328826228509007043372961063076016573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8756480687641293227/2000000000000000000)
  centralHi := (437824034382064661351/100000000000000000000)
  directionLo := (110164469121637038233/25000000000000000000)
  directionHi := (440657876486548152933/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree079.table
  base := (4614480862030834394325849666490768870699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-2996474164459507032014822766982410715500000000000)
      constant := (63324310112574725398242669634833484634609240201891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree079.table
  base := (4614480415416334602457076768032974530023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-26975208237832236157747228450572632502000000000000)
      constant := (570210952063445463273841852901729102507485971812663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110164469121637038233/25000000000000000000)
  centralHi := (440657876486548152933/100000000000000000000)
  directionLo := (88694722083488263521/20000000000000000000)
  directionHi := (221736805208720658803/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree080.table
  base := (5347705248261638576513219316357157529477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3034371287201289986424410208778784143000000000000)
      constant := (64971734026575036711002585074354125069733665134093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree080.table
  base := (5347704868286769706279969545758104554459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-27316370200200645695150146104559372287000000000000)
      constant := (585045207374485836110686517722547225611887285497579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88694722083488263521/20000000000000000000)
  centralHi := (221736805208720658803/50000000000000000000)
  directionLo := (223135789466709656939/50000000000000000000)
  directionHi := (446271578933419313879/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree081.table
  base := (1525829325289700583682071525456284740447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-768067102485768235208499412643789392625000000000)
      constant := (16660155657388758168853103601821458509763429500823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree081.table
  base := (6103316977927446190128280155871997304791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3073059129174339470283673750949568008000000000000)
      constant := (66674748714040180801119044545918850016470605433519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223135789466709656939/50000000000000000000)
  centralHi := (446271578933419313879/100000000000000000000)
  directionLo := (224526057057289952961/50000000000000000000)
  directionHi := (449052114114579905923/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree082.table
  base := (6881316548778726983927265966391617638519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3110165532684855895243585092371530998000000000000)
      constant := (68330975894276767412031678497683912777436099720271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree082.table
  base := (344065813692819179320237769657345089607/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-6999673531234366192488995353133212964250000000000)
      constant := (153823386243672632885366057601257174472007402126835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224526057057289952961/50000000000000000000)
  centralHi := (449052114114579905923/100000000000000000000)
  directionLo := (3614524302579870343/800000000000000000)
  directionHi := (112953884455620948219/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree083.table
  base := (1536340518930728035750130383151643800077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3148062655426638849653172534167904425500000000000)
      constant := (70042793797858337752401409506841064227531041047465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree083.table
  base := (3840851180426451611110244686834659023813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-14169928043652937153679449533259795821000000000000)
      constant := (315353813407091599028601409233052078255420457993653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3614524302579870343/800000000000000000)
  centralHi := (112953884455620948219/25000000000000000000)
  directionLo := (454562162135022927377/100000000000000000000)
  directionHi := (227281081067511463689/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree084.table
  base := (8504475105716062062049343379179185182559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3185959778168421804062759975964277853000000000000)
      constant := (71776076321076950939446842670435134284912949792631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree084.table
  base := (1063059363364168868932172509643564735213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-398347472912142831177247454451476825375000000000)
      constant := (8976596996838709369351870999663485521471059784117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454562162135022927377/100000000000000000000)
  centralHi := (227281081067511463689/50000000000000000000)
  directionLo := (457292289757780040803/100000000000000000000)
  directionHi := (114323072439445010201/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree085.table
  base := (9349633802156435187193969902903563249647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3223856900910204758472347417760651280500000000000)
      constant := (73530823447783563732584214830685824867728746063623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree085.table
  base := (1168704204141933590275847994152237136431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-3627772501505336672770591796811633901500000000000)
      constant := (82764451963054006277472165346689933542384582808511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457292289757780040803/100000000000000000000)
  centralHi := (114323072439445010201/25000000000000000000)
  directionLo := (460006214413414255587/100000000000000000000)
  directionHi := (115001553603353563897/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree086.table
  base := (1021717844890418609007182912196203128601/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1630877011825993856440967429778512354000000000000)
      constant := (37653517582205608455520589330603014629243288559045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree086.table
  base := (2043435661044465659616684205154685635301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-29363341974411102919567652028479810997000000000000)
      constant := (678109522488617346243425152288266286262998403844905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460006214413414255587/100000000000000000000)
  centralHi := (115001553603353563897/25000000000000000000)
  directionLo := (231352110605245310153/50000000000000000000)
  directionHi := (462704221210490620307/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree087.table
  base := (5553554424236082865257895842081149415387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1649825573196885333645761150676699067750000000000)
      constant := (38552355729781028191434785515103708279440381211283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree087.table
  base := (2776777181586582172217260423440695851983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-825125109354986457138071380068515299500000000000)
      constant := (19286019556186246240831495861371067318364700323047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231352110605245310153/50000000000000000000)
  centralHi := (462704221210490620307/100000000000000000000)
  directionLo := (232693293496532268909/50000000000000000000)
  directionHi := (465386586993064537819/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree088.table
  base := (6009712417473057805142198755931642528499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1668774134567776810850554871574885781500000000000)
      constant := (39461926161830219387085079265005918837431585442091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree088.table
  base := (6009712365577689991671512260378986401119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-15022832949573960997186743668226645283500000000000)
      constant := (355338580110402911092017386611725163658436580213039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232693293496532268909/50000000000000000000)
  centralHi := (465386586993064537819/100000000000000000000)
  directionLo := (468053580672234378823/100000000000000000000)
  directionHi := (58506697584029297353/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree089.table
  base := (6477063134467905192958028193547407881691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1687722695938668288055348592473072495250000000000)
      constant := (40382228874330769804434116733494481411389362985619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree089.table
  base := (12954126180738332772900718233413942425817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-30386827861516331531776404990440030352000000000000)
      constant := (727250891010765644761073066264512132662569490474377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468053580672234378823/100000000000000000000)
  centralHi := (58506697584029297353/12500000000000000000)
  directionLo := (235352731770393098873/50000000000000000000)
  directionHi := (470705463540786197747/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree090.table
  base := (13911213033333913232859809336816840894837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3413342514619119530520284626742518418000000000000)
      constant := (82626527727806578152570900553626538580367548606333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree090.table
  base := (6955606479198019858604998960672246719329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1707110545771374503843295702468153896500000000000)
      constant := (41334327573998185084727112003127210147108262111561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235352731770393098873/50000000000000000000)
  centralHi := (470705463540786197747/100000000000000000000)
  directionLo := (47334248957197260393/10000000000000000000)
  directionHi := (473342489571972603931/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree091.table
  base := (465333907179789076272062002450308814273/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-431404954670112810616234008567361480687500000000)
      constant := (10563757781927149602675191050781187597524434088628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree091.table
  base := (2978136993217811219129709802920786699683/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-31069151786253150606582240298413509922000000000000)
      constant := (760978176133486284979429639620234734112301917455615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47334248957197260393/10000000000000000000)
  centralHi := (473342489571972603931/100000000000000000000)
  directionLo := (237982452851696390627/50000000000000000000)
  directionHi := (95192981140678556251/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree092.table
  base := (7946271087766962262158149408747409757681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1744568380051342719669729755167632636500000000000)
      constant := (43207530663361364242002387403909899502445392125529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree092.table
  base := (3178508424290731216944906106190225934121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-31410313748621560143985157952400249707000000000000)
      constant := (778131730372540341293630107688838748710391990227005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237982452851696390627/50000000000000000000)
  centralHi := (95192981140678556251/20000000000000000000)
  directionLo := (119643238026717939889/25000000000000000000)
  directionHi := (478572952106871759557/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree093.table
  base := (16916784401229076278841150917444733459781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3527033882844468393749046952131638700500000000000)
      constant := (88341524937715088704466535008279668824075035684429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree093.table
  base := (8458392177647597893847812453611472025481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1763970872832776093410448644799277194000000000000)
      constant := (44193253278510430481194220072837072242758168855729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119643238026717939889/25000000000000000000)
  centralHi := (478572952106871759557/100000000000000000000)
  directionLo := (120291715611293438247/25000000000000000000)
  directionHi := (481166862445173752989/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree094.table
  base := (17963411648492709112302807624824433436501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3564931005586251348158634393928012128000000000000)
      constant := (90289453085026872771964800020604655500922494242909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree094.table
  base := (1122713225592651581420331134818972262043/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-4011579709169797402348874157546716159625000000000)
      constant := (101627332753154176311298121040532838013766687796566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120291715611293438247/25000000000000000000)
  centralHi := (481166862445173752989/100000000000000000000)
  directionLo := (483746864116326183087/100000000000000000000)
  directionHi := (30234179007270386443/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree095.table
  base := (19032423868305251263126197570986654343789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3602828128328034302568221835724385555500000000000)
      constant := (92258845765828945072847175691620461000620314955701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree095.table
  base := (19032423835178587230036064533159031267261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-32433799635726788756193910914360469062000000000000)
      constant := (830752039383310065463056319835653304595297406973741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483746864116326183087/100000000000000000000)
  centralHi := (30234179007270386443/6250000000000000000)
  directionLo := (486313178486277438621/100000000000000000000)
  directionHi := (243156589243138719311/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree096.table
  base := (2012382101948282877832050844943669666993/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1820362625534908628488904638760379491500000000000)
      constant := (47124851488872201330793151753313908439608639010685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree096.table
  base := (201238209913554129866584642840468375781/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-910415599947088841488800793565200245750000000000)
      constant := (23574408085169622586596551870384914201784758210725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486313178486277438621/100000000000000000000)
  centralHi := (243156589243138719311/50000000000000000000)
  directionLo := (488866021110562076853/100000000000000000000)
  directionHi := (244433010555281038427/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree097.table
  base := (10618801533712434819800174650582442704653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1839311186905800105693698359658566205250000000000)
      constant := (48131012359388146986542452466546768259241034445077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree097.table
  base := (21237603043544755827468657621054677730351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-33116123560463607830999746222333948632000000000000)
      constant := (866798617055718674985162746411927588080409023948031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488866021110562076853/100000000000000000000)
  centralHi := (244433010555281038427/50000000000000000000)
  directionLo := (245702800972800834591/50000000000000000000)
  directionHi := (491405601945601669183/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree098.table
  base := (2796721247882740221993993855655455740357/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-464564937069172895724623020139188229750000000000)
      constant := (12286976373405861595138824280763316247039736704013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree098.table
  base := (11186884981394922346658279075374569904139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-16728642761416008684201331938160344208500000000000)
      constant := (442555908668552922356036297781700888698819121349659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245702800972800834591/50000000000000000000)
  centralHi := (491405601945601669183/100000000000000000000)
  directionLo := (246966062775113750957/50000000000000000000)
  directionHi := (98786425110045500383/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree099.table
  base := (23532321741971666990804524795772731006289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3754416619295166120206571602909879265500000000000)
      constant := (100351061781746679364538342573081941452375194918201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree099.table
  base := (23532321724764227618073519876137869910791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3755383053911158545089509058923047578000000000000)
      constant := (100402032433070226790397487710344423763295185287519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246966062775113750957/50000000000000000000)
  centralHi := (98786425110045500383/20000000000000000000)
  directionLo := (496445791277972556673/100000000000000000000)
  directionHi := (248222895638986278337/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree100.table
  base := (12356629161818117749865920417754445594377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-1896156871018474537308079522353126346500000000000)
      constant := (51213888550545738527410516313581097147102122278193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree100.table
  base := (24713258309031583519849511848644112902837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-34139609447568836443208499184294167987000000000000)
      constant := (922318040726682032449297414248322346172648606904997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496445791277972556673/100000000000000000000)
  centralHi := (248222895638986278337/50000000000000000000)
  directionLo := (249473396730322169957/50000000000000000000)
  directionHi := (99789358692128867983/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree101.table
  base := (25916579710818228336349618858264616475911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3830210864778732029025746486502626120500000000000)
      constant := (104525956944286439537916584815128219119300116101599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree101.table
  base := (25916579698423872995261667683994731895357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-34480771409937245980611416838280907772000000000000)
      constant := (941211063815338229488538077522220755395460811891117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249473396730322169957/50000000000000000000)
  centralHi := (99789358692128867983/20000000000000000000)
  directionLo := (250717660791828479367/50000000000000000000)
  directionHi := (100287064316731391747/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree102.table
  base := (27142285889036468742588514333127712499939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3868107987520514983435333928298999548000000000000)
      constant := (106645601310495794255608490936361036398830891921051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree102.table
  base := (271422858785189033758153035324638868693/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-967275927008490431055953735896323543250000000000)
      constant := (26674926698780814369282851300903780458876127435925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250717660791828479367/50000000000000000000)
  centralHi := (100287064316731391747/20000000000000000000)
  directionLo := (503911560453570125343/100000000000000000000)
  directionHi := (15747236264174066417/3125000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree103.table
  base := (1774398552882846196262247207147792587767/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-488250638782787242230615171261921621937500000000)
      constant := (13598338774877177665266211568535332154062762319406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree103.table
  base := (28390376837201410897003200040937696459089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-35163095334674065055417252146254387342000000000000)
      constant := (979576932742702268273802278108483399790494428820609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503911560453570125343/100000000000000000000)
  centralHi := (15747236264174066417/3125000000000000000)
  directionLo := (506375690358254310899/100000000000000000000)
  directionHi := (5063756903582543109/1000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree104.table
  base := (29660852571865710016929659011455398249169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3943902233004080892254508811891746403000000000000)
      constant := (110949283609261495088541268034827341806810423576121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree104.table
  base := (14830426282147152908905165604912161369703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-17752128648521237296410084900120563563500000000000)
      constant := (499524889284915399974856581889443985352285352354743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506375690358254310899/100000000000000000000)
  centralHi := (5063756903582543109/1000000000000000000)
  directionLo := (101765577444014975077/20000000000000000000)
  directionHi := (254413943610037437693/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree105.table
  base := (30953713057672008836495479772349408421319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3981799355745863846664096253688119830500000000000)
      constant := (113133321540732538938629769729527078495567299085471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree105.table
  base := (30953713051248862331058703460450258682457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-3982824362156764903358120828247540768000000000000)
      constant := (113190655403672716711437374569884375678130124422913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101765577444014975077/20000000000000000000)
  centralHi := (254413943610037437693/50000000000000000000)
  directionLo := (511268322742463505259/100000000000000000000)
  directionHi := (25563416137123175263/5000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree106.table
  base := (8067239574083244053009212721569172680419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1004924119621911700268420923871123314500000000000)
      constant := (28834705998253586938963817129225175397588078457371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree106.table
  base := (32268958290884429299705986278430806748149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-36186581221779293667626005108214606697000000000000)
      constant := (1038575292928643376303985715136114221631763682410469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511268322742463505259/100000000000000000000)
  centralHi := (25563416137123175263/5000000000000000000)
  directionLo := (102739432910044508251/20000000000000000000)
  directionHi := (64212145568777817657/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree107.table
  base := (33606588281791167918787955561046283512213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3109231729729240065185358343130000000000000)
      linear := (-354405939490735414052167974258089500000000000)
      constant := (10268651494956530677503270339539229096435065733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree107.table
  base := (16803294138584872485294824777189802135931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (13991542783781580293334112544085000000000000)
      linear := (-1595237277672622203032095500139809000000000000)
      constant := (46232333018318838382583128746811120570605053539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102739432910044508251/20000000000000000000)
  centralHi := (64212145568777817657/12500000000000000000)
  directionLo := (516114576323886635431/100000000000000000000)
  directionHi := (64514322040485829429/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree108.table
  base := (34966603008958730924964009299565080880969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4095490723971212709892858579077240113000000000000)
      constant := (119814222458667812420460473478536784674082325182321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree108.table
  base := (8741650751259801203678685846130477209623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1024136254069892020623106678227446840750000000000)
      constant := (29968719561246871666654907493748087153791360557807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516114576323886635431/100000000000000000000)
  centralHi := (64514322040485829429/12500000000000000000)
  directionLo := (518520717928446511899/100000000000000000000)
  directionHi := (5185207179284465119/1000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree109.table
  base := (36349002473562448175673149036731429666809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4133387846712995664302446020873613540500000000000)
      constant := (122084118471499199640180058164645883400226198350881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree109.table
  base := (18174501235119247559096822557606850375353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-18605033554442261139917379035087413026000000000000)
      constant := (549656560590350707817135852611316915562571839052393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518520717928446511899/100000000000000000000)
  centralHi := (5185207179284465119/1000000000000000000)
  directionLo := (104183149107344260727/20000000000000000000)
  directionHi := (130228936384180325909/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree110.table
  base := (9438446668003385715528510843860256636813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1042821242363694654678008365667496742000000000000)
      constant := (31093869751011089313335205333928727731475739938517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree110.table
  base := (37753786669194898314063566528110619576549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-37551229071252931817237675724161565837000000000000)
      constant := (1119945612379051092642363011164463950104359202150869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104183149107344260727/20000000000000000000)
  centralHi := (130228936384180325909/25000000000000000000)
  directionLo := (16353119117114027883/3125000000000000000)
  directionHi := (523299811747648892257/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree111.table
  base := (9795238900324571408759942456416430542781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1052295523049140393280405226116590098875000000000)
      constant := (31672076014032337412916255566290771054486467131429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree111.table
  base := (39180955598908326524916074599717220900639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4210265670402371261626732597572033958000000000000)
      constant := (126752375310930897370524039792035265586277827607351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16353119117114027883/3125000000000000000)
  centralHi := (523299811747648892257/100000000000000000000)
  directionLo := (262836532849873895911/50000000000000000000)
  directionHi := (525673065699747791823/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree112.table
  base := (40630509258886080596493258747781476268573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4247079214938344527531208346262733823000000000000)
      constant := (129022593627608124988484244371367658809988215968357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree112.table
  base := (2031525462842988512148121110316825067387/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-9558388248997437723010877758033761351750000000000)
      constant := (290447604359343479601566267545085637409428164567735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262836532849873895911/50000000000000000000)
  centralHi := (525673065699747791823/100000000000000000000)
  directionLo := (5280356531799893029/1000000000000000000)
  directionHi := (528035653179989302901/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree113.table
  base := (21051223821326118588864590548151005357427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2142488168840063740970397894029553625250000000000)
      constant := (65689173859179029001657738558478930021225358065643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree113.table
  base := (21051223820467189355355970260162254400997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-19287357479179080214723214343060892596000000000000)
      constant := (591501365647470051301341580425459843079438217791957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5280356531799893029/1000000000000000000)
  centralHi := (528035653179989302901/100000000000000000000)
  directionLo := (530387716728304838319/100000000000000000000)
  directionHi := (6629846459103810479/1250000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree114.table
  base := (4359677075081308135375510754780361524769/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2161436730210955218175191614927740339000000000000)
      constant := (66877783164138102501978815607029009310479408482605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree114.table
  base := (871935414987136670214869035698032377267/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2161993162262587220380519241117140276500000000000)
      constant := (66911573298341915324707562385288914663920748505075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530387716728304838319/100000000000000000000)
  centralHi := (6629846459103810479/1250000000000000000)
  directionLo := (532729395737940412783/100000000000000000000)
  directionHi := (33295587233621275799/6250000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree115.table
  base := (11278369645467858659583908604637720293267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1090192645790923347689992667912963526375000000000)
      constant := (34038562364319039304727528926046230630091024084203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree115.table
  base := (1804539143225482026977170829959933144371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-39257038883094979504252263994095264762000000000000)
      constant := (1226007181662243044291936463875453446200923886891275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532729395737940412783/100000000000000000000)
  centralHi := (33295587233621275799/6250000000000000000)
  directionLo := (4180162707436392397/781250000000000000)
  directionHi := (535060826551858226817/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree116.table
  base := (46652571134570804356768126568877922457579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4398667705905476345169558113448227533000000000000)
      constant := (138574397105285396916039638749510122670786999555811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree116.table
  base := (11663142783381140164043948973454733163297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-9899550211365847260413795412020501136750000000000)
      constant := (311949829542639069236779071069782366039201481618257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4180162707436392397/781250000000000000)
  centralHi := (535060826551858226817/100000000000000000000)
  directionLo := (537382142555373998789/100000000000000000000)
  directionHi := (53738214255537399879/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree117.table
  base := (24107024203928446695604533304079886205589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2218282414323629649789572777622300480250000000000)
      constant := (70508004636121537980139729194676238489533446631901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree117.table
  base := (48214048406970179350135661161757989233647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4437706978647977619895344366896527148000000000000)
      constant := (141087192099394355160540557395581810620023299519623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537382142555373998789/100000000000000000000)
  centralHi := (53738214255537399879/10000000000000000000)
  directionLo := (53969347426520814963/10000000000000000000)
  directionHi := (539693474265208149631/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree118.table
  base := (12449477600211314996428342354070847541617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1118615487847260563497183249260243597000000000000)
      constant := (35869771489524537329597570449887491819587278059353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree118.table
  base := (49797910400093804979447114045256105828167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-40280524770200208116461016956055484117000000000000)
      constant := (1291963413833764651799979827432671415124627025624727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53969347426520814963/10000000000000000000)
  centralHi := (539693474265208149631/100000000000000000000)
  directionLo := (270997474707559535267/50000000000000000000)
  directionHi := (108398989883023814107/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree119.table
  base := (514041571127941450486709038480736082717/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1128089768532706302099580109709336953875000000000)
      constant := (36490906790701951700694863350661578894419981731325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree119.table
  base := (51404157112157361908381700713619667804933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-40621686732568617653863934610042223902000000000000)
      constant := (1314335372987819264620440413920534410533117318416373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270997474707559535267/50000000000000000000)
  centralHi := (108398989883023814107/20000000000000000000)
  directionLo := (68035836629784682003/12500000000000000000)
  directionHi := (21771467721531098241/4000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree120.table
  base := (53032788543081641380590830820198218462787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4550256196872608162807907880633721243000000000000)
      constant := (148469632886336155406975514320032901726432640197883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree120.table
  base := (26516394271271034440472498577740465948407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2275713816385390399514825125779386871500000000000)
      constant := (74272255908688423419768711834545655252596934496463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68035836629784682003/12500000000000000000)
  centralHi := (21771467721531098241/4000000000000000000)
  directionLo := (546568827546532018399/100000000000000000000)
  directionHi := (683211034433165023/125000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree121.table
  base := (54683804691186511158246057125251536803551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4588153319614391117217495322430094670500000000000)
      constant := (150997103128653112198062466394456392252989945066359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree121.table
  base := (13670951172682335158715566126674543462157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-10326002664326359182167442479503925868000000000000)
      constant := (339914778484803088507203588948493532249212596081917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546568827546532018399/100000000000000000000)
  centralHi := (683211034433165023/125000000000000000)
  directionLo := (109768294561341754781/20000000000000000000)
  directionHi := (274420736403354386953/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree122.table
  base := (28178602778336034415949020924852318874063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2313025221178087035813541382113234049000000000000)
      constant := (76773018944866737063809154816285072557533591473767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree122.table
  base := (56357205556284742275668177103828084268173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-41645172619673846266072687572002443257000000000000)
      constant := (1382610895736055803660725649462067942324258219842813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109768294561341754781/20000000000000000000)
  centralHi := (274420736403354386953/50000000000000000000)
  directionLo := (275552373107039233931/50000000000000000000)
  directionHi := (551104746214078467863/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree123.table
  base := (29026495569586319854706880752113798826717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2331973782548978513018335103011420762750000000000)
      constant := (78058218584778068248450164817152182981794490065253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree123.table
  base := (58052991138844508580573949742016773274749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4665148286893583978163956136221020338000000000000)
      constant := (156195105749637002221993180155196495428514133158341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275552373107039233931/50000000000000000000)
  centralHi := (551104746214078467863/100000000000000000000)
  directionLo := (553358762763119550629/100000000000000000000)
  directionHi := (55335876276311955063/10000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree124.table
  base := (3735697589898886421233197608798128533801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-587730585979967497555782205977401869125000000000)
      constant := (19838537621012929540939592638829430996268722477218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree124.table
  base := (59771161438104218357562118089569612202743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-42327496544410665340878522879975922827000000000000)
      constant := (1429094281971085877637794000353834659436764503814983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553358762763119550629/100000000000000000000)
  centralHi := (55335876276311955063/10000000000000000000)
  directionLo := (277801817557848698187/50000000000000000000)
  directionHi := (4444829080925579171/800000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree125.table
  base := (61511716454044731746062800705288815850939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4739741810581522934855845089615588380500000000000)
      constant := (161321629285360600682850267336335423669428026480051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree125.table
  base := (61511716453809279482227237692468867015371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-42668658506779074878281440533962662612000000000000)
      constant := (1452625886408982133874326754005852893305600580626651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277801817557848698187/50000000000000000000)
  centralHi := (4444829080925579171/800000000000000000)
  directionLo := (139459868416693535587/25000000000000000000)
  directionHi := (557839473666774142349/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree126.table
  base := (7909332023243295574263009265403049251361/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-597204866665413236158179066426495226000000000000)
      constant := (20494552765164410396668437431214902355887067560649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree126.table
  base := (6327465618574693526469175916072060397093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2389434470508193578649131010441633466500000000000)
      constant := (82019486947795070920443509496895381492652639065185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139459868416693535587/25000000000000000000)
  centralHi := (557839473666774142349/100000000000000000000)
  directionLo := (280033193303878795113/50000000000000000000)
  directionHi := (560066386607757590227/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree127.table
  base := (65059980633908456190681596086568658520207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4815536056065088843675019973208335235500000000000)
      constant := (166612679475957174557323365548577215768697811562663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree127.table
  base := (32529990316869774517268539567299913834689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-21675491215757946976543637920968071091000000000000)
      constant := (750134458962490517979856906944509548757417494004209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280033193303878795113/50000000000000000000)
  centralHi := (560066386607757590227/100000000000000000000)
  directionLo := (14057111999689800691/2500000000000000000)
  directionHi := (562284479987592027641/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree128.table
  base := (13373537959556402040767304006709671860811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4853433178806871798084607415004708663000000000000)
      constant := (169290401349277675599535692991274989314153185628495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree128.table
  base := (16716922449409740669670734777661964758329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-10923036098471075872622548373980720491750000000000)
      constant := (381095086250728613582025960559677626544252074563049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14057111999689800691/2500000000000000000)
  centralHi := (562284479987592027641/100000000000000000000)
  directionLo := (35280866110730535851/6250000000000000000)
  directionHi := (564493857771688573617/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree129.table
  base := (34348891838721448580509984414067748015461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2445665150774327376247097428400541045250000000000)
      constant := (85994793870634811120418420805146535418438879477549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree129.table
  base := (858722295966521968830080002983825845519/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-611573699392398792054070988193189191000000000000)
      constant := (21509514531861769782527800030650981786877418832710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35280866110730535851/6250000000000000000)
  centralHi := (564493857771688573617/100000000000000000000)
  directionLo := (141673655474696926153/25000000000000000000)
  directionHi := (566694621898787704613/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree130.table
  base := (35275131136393927056639999935131392016479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2464613712145218853451891149298727759000000000000)
      constant := (87355119325963527360578226434533326821015903745911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree130.table
  base := (35275131136342636619663850891044494911471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-22187234159310561282648014401948180768500000000000)
      constant := (786591510899163310602878461738593394778671504770751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141673655474696926153/25000000000000000000)
  centralHi := (566694621898787704613/100000000000000000000)
  directionLo := (113777374467168391567/20000000000000000000)
  directionHi := (142221718083960489459/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree131.table
  base := (72425125583731124186368145112141030100863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-4967124547032220661313369740393828945500000000000)
      constant := (177452354081245023633179589115062200686953768434967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree131.table
  base := (1448502511672885279314630262744847190627/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-22357815140494766051349473228941550661000000000000)
      constant := (798937135757853882831320478855722539502465719999675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113777374467168391567/20000000000000000000)
  centralHi := (142221718083960489459/25000000000000000000)
  directionLo := (285535353565501208447/50000000000000000000)
  directionHi := (114214141426200483379/20000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree132.table
  base := (9290296701275204222158899574100840039229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-625627708721750451965369647773775296625000000000)
      constant := (22526991753652428375739105303952325961892638550661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree132.table
  base := (743223736101280892583349395003940742049/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1251577562315498378891718447551940030750000000000)
      constant := (45076633206837615693834567976804601560209487101025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285535353565501208447/50000000000000000000)
  centralHi := (114214141426200483379/20000000000000000000)
  directionLo := (143311555616197111039/25000000000000000000)
  directionHi := (573246222464788444157/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree133.table
  base := (38121003176070310743590125368598442916057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2521459396257893285066272311993287900250000000000)
      constant := (91500489247923436729975971822481564141111091365313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree133.table
  base := (76242006352078354920924336728664650659097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-45397954205726351177504781765856580892000000000000)
      constant := (1647836593589635487473255887252765112673206194458057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143311555616197111039/25000000000000000000)
  centralHi := (573246222464788444157/100000000000000000000)
  directionLo := (575413512699516218369/100000000000000000000)
  directionHi := (57541351269951621837/10000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree134.table
  base := (78184023809499646605406439879254967262773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5080815915257569524542132065782949228000000000000)
      constant := (185807487481124567268307944774870098762260291396157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree134.table
  base := (9773002976180866437061405152321102892923/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-5717389521011845089363462427480415084625000000000)
      constant := (209138458243265841659971833563873123305614171047563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575413512699516218369/100000000000000000000)
  centralHi := (57541351269951621837/10000000000000000000)
  directionLo := (577572670427057950081/100000000000000000000)
  directionHi := (288786335213528975041/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree135.table
  base := (80148425982238916490042971540065212444759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5118713037999352478951719507579322655500000000000)
      constant := (188635460985050211822170646660333251538489960832431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree135.table
  base := (80148425982194290152929186410817663616801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5120030903384796694701179674870006718000000000000)
      constant := (188730223612845263327661047384077406889279472185609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577572670427057950081/100000000000000000000)
  centralHi := (288786335213528975041/50000000000000000000)
  directionLo := (115944757303000033481/20000000000000000000)
  directionHi := (289861893257500083703/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree136.table
  base := (82135212870325881880463647327034586526463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5156610160741135433361306949375696083000000000000)
      constant := (191484899007621928560199621291207329626934174905367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree136.table
  base := (20533803217572026302739556368001108600411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-11605360023207894947428383681954200061750000000000)
      constant := (431057408324515151640875917499131679363457842198891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115944757303000033481/20000000000000000000)
  centralHi := (289861893257500083703/50000000000000000000)
  directionLo := (581866950151266177547/100000000000000000000)
  directionHi := (145466737537816544387/25000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree137.table
  base := (84144384473734057318294232795582000580751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5194507283482918387770894391172069510500000000000)
      constant := (194355801548838188889817705625695892227586950741159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree137.table
  base := (657378003700797505358650430633205772967/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-5845325256899998665889556547725442504000000000000)
      constant := (218760066036684098026063513382908292520475590736432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (581866950151266177547/100000000000000000000)
  centralHi := (145466737537816544387/25000000000000000000)
  directionLo := (584002248887264703461/100000000000000000000)
  directionHi := (292001124443632351731/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree138.table
  base := (86175940792442030694538737537294332223967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5232404406224701342180481832968442938000000000000)
      constant := (197248168608697757023808752494007707354230911040503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree138.table
  base := (2692998149762967657082436708638525639991/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-654218944688449984229435694941531664125000000000)
      constant := (24668398576414345336076864096486530359523709321276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584002248887264703461/100000000000000000000)
  centralHi := (292001124443632351731/50000000000000000000)
  directionLo := (586129768679623758611/100000000000000000000)
  directionHi := (146532442169905939653/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree139.table
  base := (44114940913216315844416048569016121164281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2635150764483242148295034637382408182750000000000)
      constant := (100081000093599820993640275769616895902734494824929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree139.table
  base := (44114940913204861979103356300989406719281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-23722462989968404200961143844888509801000000000000)
      constant := (901181070461565999211290968024407549601512886379361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586129768679623758611/100000000000000000000)
  centralHi := (146532442169905939653/25000000000000000000)
  directionLo := (294124796965283022871/50000000000000000000)
  directionHi := (588249593930566045743/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree140.table
  base := (90306207575692233696879893362118653801637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5308198651708267250999656716561189793000000000000)
      constant := (203097296284343057328819573550903220362037082687533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree140.table
  base := (45153103787836423071863407139233500955093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-23893043971152608969662602671881879693500000000000)
      constant := (914396429278681584347121175913300887763117152315333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294124796965283022871/50000000000000000000)
  centralHi := (588249593930566045743/100000000000000000000)
  directionLo := (590361807526979538107/100000000000000000000)
  directionHi := (147590451881744884527/25000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree141.table
  base := (92404918040210167900704983547125432706873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5346095774450050205409244158357563220500000000000)
      constant := (206054056900127387303901539164745266768827695433057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree141.table
  base := (92404918040193760421423020280219392766103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5347472211630403052969791444194499908000000000000)
      constant := (206157427822724542670814082209246450186209509878127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590361807526979538107/100000000000000000000)
  centralHi := (147590451881744884527/25000000000000000000)
  directionLo := (592466490878234414623/100000000000000000000)
  directionHi := (18514577839944825457/3125000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree142.table
  base := (94526013219978231546590315796708315702089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7061613583350539477545559942570000000000000)
      linear := (-1068040646140018480424287165275528000000000000)
      constant := (41466431667239071314311346196655443881473216961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree142.table
  base := (94526013219964346767822002175842814224331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030410000000000000000000000000000000000000000
      center := (18135216)
      previous := (9067608)
      next := (9067608)
      square := (63554522250154855297910039483130000000000000)
      linear := (-9614840679833770484850434566898877000000000000)
      constant := (373385065753739521259796198516075608420489290571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592466490878234414623/100000000000000000000)
  centralHi := (18514577839944825457/3125000000000000000)
  directionLo := (7432046549409939569/1250000000000000000)
  directionHi := (594563723952795165521/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree143.table
  base := (96669493114990275361139922091811765714963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5421890019933616114228419041950310075500000000000)
      constant := (212031971687617016001765616871485006814766802001867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree143.table
  base := (96669493114978525990546128128858524694719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-48809573829410446551533958305723978742000000000000)
      constant := (1909244656737600138881202591399201449734183512554639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7432046549409939569/1250000000000000000)
  centralHi := (594563723952795165521/100000000000000000000)
  directionLo := (298326792656837227149/50000000000000000000)
  directionHi := (596653585313674454299/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree144.table
  base := (98835357725241857443687510856696693996641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5459787142675399068638006483746683503000000000000)
      constant := (215053125859321703461196109522664549148269983300169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree144.table
  base := (12354419715653989443866976617983369165351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-682649108219150779013012166107093312875000000000)
      constant := (26895117655882170059005259519674614624707056242559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298326792656837227149/50000000000000000000)
  centralHi := (596653585313674454299/100000000000000000000)
  directionLo := (74842019019096650987/12500000000000000000)
  directionHi := (598736152152773207897/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree145.table
  base := (126279508813412441245595677793700552027/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-687210533177147752880949240692882116312500000000)
      constant := (27261968068708255787415013863397686910137611954300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree145.table
  base := (101023607050721540930537335442657596107967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-49491897754147265626339793613697458312000000000000)
      constant := (1963845559922347697718989373766788725537963140368527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74842019019096650987/12500000000000000000)
  centralHi := (598736152152773207897/100000000000000000000)
  directionLo := (600811500324149402917/100000000000000000000)
  directionHi := (300405750162074701459/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree146.table
  base := (5161712054572635547702540586071056227697/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1383895347039741244364295341834857589500000000000)
      constant := (55289956939662484420747198966659033834655258930365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree146.table
  base := (25808560272861398411885256186569500202049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80094586665757656389191127258614582500000000000)
      linear := (-12458264929128918790935677816921049524250000000000)
      constant := (497858980708523389978476291200620401382279747616369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600811500324149402917/100000000000000000000)
  centralHi := (300405750162074701459/50000000000000000000)
  directionLo := (602879704376256115233/100000000000000000000)
  directionHi := (301439852188128057617/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree147.table
  base := (105467259847409250001751019903172298475123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5573478510900747931866768809135803785500000000000)
      constant := (224245375486273326747647459899058526914694575147307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree147.table
  base := (105467259847403228450946937997395440161647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5574913519876009411238403213518993098000000000000)
      constant := (224357728884305932420518754808249813991099321071623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (602879704376256115233/100000000000000000000)
  centralHi := (301439852188128057617/50000000000000000000)
  directionLo := (18904401174474612413/3125000000000000000)
  directionHi := (604940837583187597217/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree148.table
  base := (26930665829649871918371441197838972704711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1402843908410632721569089062733044303250000000000)
      constant := (56838096933134052183453593799670075441569526880799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree148.table
  base := (53861331659297196707382877018026996152379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-25257691820626247119274273287828838833500000000000)
      constant := (1023598235648163583179690095241283216121318451361099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18904401174474612413/3125000000000000000)
  centralHi := (604940837583187597217/100000000000000000000)
  directionLo := (606994971974970435611/100000000000000000000)
  directionHi := (151748742993742608903/25000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree149.table
  base := (55000225752511998613740880100422130779191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2824636378192156920342971846364275320250000000000)
      constant := (115240432248719308363374650470669476779832343063119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree149.table
  base := (110000451505019687658224614323593875977609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-50856545603620903775951464229644417452000000000000)
      constant := (2075366656846815194838348391483241748149978006012729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606994971974970435611/100000000000000000000)
  centralHi := (151748742993742608903/25000000000000000000)
  directionLo := (609042178366935218409/100000000000000000000)
  directionHi := (60904217836693521841/10000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree150.table
  base := (3509394512708871495191974591345773932199/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-710896234890762099386941391815615508500000000000)
      constant := (29203850722622576842782395952567608045374760421564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree150.table
  base := (112300624406680242261235592238575458887691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5688634173998812590372709098181239693000000000000)
      constant := (233747790734468673859783478895483164186606883439619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609042178366935218409/100000000000000000000)
  centralHi := (60904217836693521841/10000000000000000000)
  directionLo := (305541263194101298033/50000000000000000000)
  directionHi := (611082526388202596067/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree151.table
  base := (57311591011790352209098795633346304365039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2862533500933939874752559288160648747750000000000)
      constant := (118401105791581145971341928166755677605652971146951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree151.table
  base := (2865579550589440516323022027040220998079/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-6442358691044715356344662442202237127750000000000)
      constant := (266535856323317073518747394148380357700242757913995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305541263194101298033/50000000000000000000)
  centralHi := (611082526388202596067/100000000000000000000)
  directionLo := (153279021127329039111/25000000000000000000)
  directionHi := (122623216901863231289/20000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree152.table
  base := (29242031088929085939899757169475501860849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1440741031152415675978676504529417730750000000000)
      constant := (59998770475995939450408784290369900590127300273241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree152.table
  base := (4678724974228549413852103184456228856893/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-51880031490726132388160217191604636807000000000000)
      constant := (2161036858775771758490160897970513015433973141028325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153279021127329039111/25000000000000000000)
  centralHi := (122623216901863231289/20000000000000000000)
  directionLo := (615142920069053139539/100000000000000000000)
  directionHi := (30757146003452656977/5000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree153.table
  base := (59667725701546492316183911993129691427447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2900430623675722829162146729957022175250000000000)
      constant := (121604708371722569032537682398986028759103094983823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree153.table
  base := (59667725701545389196222743778588111844593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2901177414060807884753507491421743144000000000000)
      constant := (121665563398773595243054548280190635463724084840537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615142920069053139539/100000000000000000000)
  centralHi := (30757146003452656977/5000000000000000000)
  directionLo := (617163099300442693441/100000000000000000000)
  directionHi := (308581549650221346721/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree154.table
  base := (24345032633142605868587581558443631800259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5838758370093228612733880901710417778000000000000)
      constant := (246445216101546571380700610445140905184702771159655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree154.table
  base := (121725163165711163347587950402853733554217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-52562355415462951462966052499578116377000000000000)
      constant := (2219116697792996709477189025760485440087725932514777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617163099300442693441/100000000000000000000)
  centralHi := (308581549650221346721/50000000000000000000)
  directionLo := (154794171839005028279/25000000000000000000)
  directionHi := (619176687356020113117/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree155.table
  base := (124137259643579055056486166124901182887831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-5876655492835011567143468343506791205500000000000)
      constant := (249702479978288206488075953460617327263303329456879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree155.table
  base := (124137259643577476899879577235321694732401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-52903517377831361000368970153564856162000000000000)
      constant := (2248446528620989087399382766049949589109105431794081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154794171839005028279/25000000000000000000)
  centralHi := (619176687356020113117/100000000000000000000)
  directionLo := (621183748332344305087/100000000000000000000)
  directionHi := (9705996067692879767/1562500000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree156.table
  base := (63285870418346886630956764260014202759223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-2957276307788397260776527892651582316500000000000)
      constant := (126490604186835099939590410526053022557854724744207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree156.table
  base := (3955366901146638706218635368172722070771/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-739509435280552368580165108438216610375000000000)
      constant := (31638467134193100843838663047276104669818217757356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621183748332344305087/100000000000000000000)
  centralHi := (9705996067692879767/1562500000000000000)
  directionLo := (77898043161725572547/12500000000000000000)
  directionHi := (623184345293804580377/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree157.table
  base := (32257151686264999018173192645527211664619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1488112434579644368990660806774884515125000000000)
      constant := (64070350321923178463370583850302728638211704295171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree157.table
  base := (129028606745058867381139445636677546886893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-53585841302568180075174805461538335732000000000000)
      constant := (2307686012915740693787323710901581075192696374071133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77898043161725572547/12500000000000000000)
  centralHi := (623184345293804580377/100000000000000000000)
  directionLo := (312589270147870896117/50000000000000000000)
  directionHi := (125035708059148358447/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree158.table
  base := (16438482171085076032413075331955223416383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-748793357632545053796528833611988936000000000000)
      constant := (32450382340044489362975486418920612247486380762647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree158.table
  base := (131507857368679653791320734998664543263479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-53927003264936589612577723115525075517000000000000)
      constant := (2337595666382502887927076084371955634574359595920199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312589270147870896117/50000000000000000000)
  centralHi := (125035708059148358447/20000000000000000000)
  directionLo := (627166394406907801017/100000000000000000000)
  directionHi := (313583197203453900509/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree159.table
  base := (67004746353779272042923626878146543739949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-3014121991901071692390909055346142457750000000000)
      constant := (131473090335829986189731884054076901122484431225141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree159.table
  base := (8375593294222358561297424883551712090593/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-753724517045902765971953344020997434750000000000)
      constant := (32884702695308213470250288153823795528352833909074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627166394406907801017/100000000000000000000)
  centralHi := (313583197203453900509/50000000000000000000)
  directionLo := (629147967731286263501/100000000000000000000)
  directionHi := (314573983865643131751/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree160.table
  base := (136533512761696768171999611235450640446253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-6066141106543926339191405552488658343000000000000)
      constant := (266310767141605057381734642424840554942026988159477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree160.table
  base := (136533512761696085705006833361202958412861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-54609327189673408687383558423498555087000000000000)
      constant := (2397994795954807681639907663788366191384648655527341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629147967731286263501/100000000000000000000)
  centralHi := (314573983865643131751/50000000000000000000)
  directionLo := (15778082985732420131/2500000000000000000)
  directionHi := (631123319429296805241/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree161.table
  base := (139079917531098259726359853604514830284977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-6104038229285709293600992994285031770500000000000)
      constant := (269696818130191341853880045892687128999163999133593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree161.table
  base := (69539958765548841336298776569438457575197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160189173331515312778382254517229165000000000000)
      linear := (-27475244576020909112393238038742647436000000000000)
      constant := (1214242136030176686290039248662978705403104111222157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15778082985732420131/2500000000000000000)
  centralHi := (631123319429296805241/100000000000000000000)
  directionLo := (126618501547680747953/20000000000000000000)
  directionHi := (316546253869201869883/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree162.table
  base := (141648707015765999602064955307846036137373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-6141935352027492248010580436081405198000000000000)
      constant := (273104333637418997834077094787797887081536125507557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree162.table
  base := (70824353507882755849149997301166939889293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-3071758395245012653454966318415113036500000000000)
      constant := (136620390132157221808915938429693920844049070922837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126618501547680747953/20000000000000000000)
  centralHi := (316546253869201869883/50000000000000000000)
  directionLo := (317527794996574822659/50000000000000000000)
  directionHi := (635055589993149645319/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree163.table
  base := (28847976243140591942741983345349681340287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-6179832474769275202420167877877778625500000000000)
      constant := (276533313663288196844620238031534572780496210476915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree163.table
  base := (18029985151962818400338721551740920035397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40047293332878828194595563629307291250000000000)
      linear := (-6954101634597329662449038923182346805250000000000)
      constant := (311255380863779885822934248371003861238367147418357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317527794996574822659/50000000000000000000)
  centralHi := (635055589993149645319/100000000000000000000)
  directionLo := (637012622644633296081/100000000000000000000)
  directionHi := (318506311322316648041/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree164.table
  base := (73426720065456047214304139440955970259753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-3108864798755529078414877659837076026500000000000)
      constant := (139991879103899554697536472780801783067063220880977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree164.table
  base := (146853440130911745673504415781988135620351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-55973975039147046836995229039445514227000000000000)
      constant := (2521112345654582190336491002454129794004063657038031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637012622644633296081/100000000000000000000)
  centralHi := (318506311322316648041/50000000000000000000)
  directionLo := (638963661279450668543/100000000000000000000)
  directionHi := (1247975900936427087/195312500000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree165.table
  base := (9343086485087270850476167650870113550379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4449699259208758688288395958811921250000000000)
      linear := (-781953340031605138904917845183815685062500000000)
      constant := (35431958408868988072577890756889952771868687672022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree165.table
  base := (149489383761396038765528879622043491450293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-6257237444612828486044238521492472668000000000000)
      constant := (283597213179095647400897650581002111935725213371837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638963661279450668543/100000000000000000000)
  centralHi := (1247975900936427087/195312500000000000)
  directionLo := (80113595079764625347/12500000000000000000)
  directionHi := (640908760638117002777/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree166.table
  base := (152147712107158577022997603371216129520113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-6293523842994624065648930203266898908000000000000)
      constant := (286949040852746749759912796623641000868895775408217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree166.table
  base := (152147712107158327768815245495888286974457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-56656298963883865911801064347418993797000000000000)
      constant := (2583830765782076502414393397898107615661778654658217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80113595079764625347/12500000000000000000)
  centralHi := (640908760638117002777/100000000000000000000)
  directionLo := (642847974632987191143/100000000000000000000)
  directionHi := (80355996829123398893/12500000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree167.table
  base := (30965685033640337984923093378959975562313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-6331420965736407020058517645063272335500000000000)
      constant := (290463878953183810299144866180759547407947937340085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree167.table
  base := (154828425168201479217266448350178122585427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-56997460926252275449203982001405733582000000000000)
      constant := (2615479887165230706718225407645700689253602241858787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642847974632987191143/100000000000000000000)
  centralHi := (80355996829123398893/12500000000000000000)
  directionLo := (5158250850925528733/800000000000000000)
  directionHi := (322390678182845545813/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree168.table
  base := (15753152294452849956272773119528289161621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17798797036835034753153583835247685000000000000)
      linear := (-3184659044239094987234052543429822881500000000000)
      constant := (147000090786131624685698461798062402828220307484945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree168.table
  base := (31506304588905664289475066260996475047361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35597594073670069506307167670495370000000000000)
      linear := (-6370958098735631665178544406154719263000000000000)
      constant := (294146920306813878737944124736937656596208435623245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell206.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5158250850925528733/800000000000000000)
  centralHi := (322390678182845545813/50000000000000000000)
  directionLo := (16167723953602492947/2500000000000000000)
  directionHi := (646708958144099717881/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree169.table
  base := (40064251359035448126611632618801589821351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8899398518417517376576791917623842500000000000)
      linear := (-1601803802804993232219423132164004797625000000000)
      constant := (74389487177496306950464603337491281649557501046559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree169.table
  base := (160257005436141641947123892430543893445281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320378346663030625556764509034458330000000000000)
      linear := (-57679784850989094524009817309379213152000000000000)
      constant := (2679357952570360556088201823449691134396155300785361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell206.Kernel169
