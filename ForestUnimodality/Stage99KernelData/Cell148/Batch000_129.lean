import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell148.Parameters
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q113_213.Batch000_049
import ForestUnimodality.BinomialMassData.Q113_213.Batch050_099
import ForestUnimodality.BinomialMassData.Q113_213.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree000.table
  base := (5323109882058756863298043571/100000000000000000000000000)
  polynomial :=
    { denominator := 120416000000000000000000000000000000000000000
      center := (734459)
      previous := (0)
      next := (650325)
      square := (16692824186981695821607729644800000000000000)
      linear := (-76682384393161928958448925189440000000000000)
      constant := (6409875995579872664508972146455360000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree000.table
  base := (5323109882058756863298043571/100000000000000000000000000)
  polynomial :=
    { denominator := 426000000000000000000000000000000000000000
      center := (2599)
      previous := (0)
      next := (2300)
      square := (59054802548284301255687722800000000000000)
      linear := (-271282020258827578862437235340000000000000)
      constant := (22676448097570304237649665612460000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree001.table
  base := (319262623304131374920833165263698775122537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-1775936534084145751272841296656437600000000000000)
      constant := (73186571229002573624215612328986472508249914060048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree001.table
  base := (159603621306640705147187800986831283654811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-355647278455212631907422782401100000000000000)
      constant := (14653088923440010389053364205892197016270240518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49906787853214316469/100000000000000000000)
  directionHi := (4990678785321431647/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree002.table
  base := (50058895058924535107286288160987367715311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-2109094005810949809192466065873561600000000000000)
      constant := (47249749910532572903660460632315469057692649443776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree002.table
  base := (200173882312899264694782718876431779516407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-422379205334773892326349909165100000000000000)
      constant := (9459042317033635917454393176567033404879869183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906787853214316469/100000000000000000000)
  centralHi := (4990678785321431647/10000000000000000000)
  directionLo := (70578856236492527093/100000000000000000000)
  directionHi := (35289428118246263547/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree003.table
  base := (132192995539266707799678582924576573488659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-2442251477537753867112090835090685600000000000000)
      constant := (33040804743952273284316319978816864719645296373936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree003.table
  base := (132140341931470941357468662390668714084391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-163037044071445050915092345309700000000000000)
      constant := (2204736308091298138257957065247182963098245093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70578856236492527093/100000000000000000000)
  centralHi := (35289428118246263547/50000000000000000000)
  directionLo := (86441092204328492787/100000000000000000000)
  directionHi := (21610273051082123197/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree004.table
  base := (11500716030278303265336688208479849325153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-2775408949264557925031715604307809600000000000000)
      constant := (25319535009309815756872447260490009540953911149696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree004.table
  base := (91964567482649500048086848914012921931757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-555843059093896413164204162693100000000000000)
      constant := (5068656897854211549519728111960252255121883333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86441092204328492787/100000000000000000000)
  centralHi := (21610273051082123197/25000000000000000000)
  directionLo := (49906787853214316469/50000000000000000000)
  directionHi := (99813575706428632939/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree005.table
  base := (67209935287013281582346083819999221721977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-3108566420991361982951340373524933600000000000000)
      constant := (21262098721251869698117904712704875326226645345808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree005.table
  base := (67178525790553331652260400713897846405213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-622574985973457673583131289457100000000000000)
      constant := (4256724040618014597781799359374331393558108597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906787853214316469/50000000000000000000)
  centralHi := (99813575706428632939/100000000000000000000)
  directionLo := (4463798807137920317/4000000000000000000)
  directionHi := (55797485089224003963/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree006.table
  base := (51062963611445947217817896417235517735629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-3441723892718166040870965142742057600000000000000)
      constant := (19340862169876753533501568828887587203024063380816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree006.table
  base := (51038765208880095258616392823057795334783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-229768970951006311334019472073700000000000000)
      constant := (1290822231608070884917335568381303038847923309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4463798807137920317/4000000000000000000)
  centralHi := (55797485089224003963/50000000000000000000)
  directionLo := (122246164941704573117/100000000000000000000)
  directionHi := (61123082470852286559/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree007.table
  base := (39896310970218642890282013800113328523631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-3774881364444970098790589911959181600000000000000)
      constant := (18724679566857918407941315037378898791754167258224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree007.table
  base := (1246160034459862868397061968406656066287/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-756038839732580194420985542985100000000000000)
      constant := (3749463899151384329820204625116230530283996896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246164941704573117/100000000000000000000)
  centralHi := (61123082470852286559/50000000000000000000)
  directionLo := (6602047469683208113/5000000000000000000)
  directionHi := (132040949393664162261/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree008.table
  base := (31697054901925685024773050818494565320869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-4108038836171774156710214681176305600000000000000)
      constant := (18957497756396957009724598972162078728400708269776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree008.table
  base := (3960156956901531428949699657453284276493/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-822770766612141454839912669749100000000000000)
      constant := (3796417899186969506094238540656784434721687336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6602047469683208113/5000000000000000000)
  centralHi := (132040949393664162261/100000000000000000000)
  directionLo := (70578856236492527093/50000000000000000000)
  directionHi := (141157712472985054187/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree009.table
  base := (25346728559089901528394680812636728347597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-4441196307898578214629839450393429600000000000000)
      constant := (19785913865195085651211489673538578319145028222288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree009.table
  base := (25333226992892517905626307092483489180041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-296500897830567571752946598837700000000000000)
      constant := (1320869596691055884923750769574927806869760043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70578856236492527093/50000000000000000000)
  centralHi := (141157712472985054187/100000000000000000000)
  directionLo := (4678761361238842169/3125000000000000000)
  directionHi := (149720363559642949409/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree010.table
  base := (20212338040464973662630073928950870463457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-4774353779625382272549464219610553600000000000000)
      constant := (21066515083370429388957745220371361595354551107728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree010.table
  base := (10100216231980128856945998829199599019433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-956234620371263975677766923277100000000000000)
      constant := (4219336022100639087850384619634913215825311554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4678761361238842169/3125000000000000000)
  centralHi := (149720363559642949409/100000000000000000000)
  directionLo := (39454780079745565941/25000000000000000000)
  directionHi := (31563824063796452753/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree011.table
  base := (3981542028702390639669814471139387431427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-5107511251352186330469088988827677600000000000000)
      constant := (22715990853830965212267742657126209284470862794432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree011.table
  base := (397885567972504403330467554459734983717/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-204593309450165047219338810008220000000000000)
      constant := (909985757146244879807173007318289731810052584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39454780079745565941/25000000000000000000)
  centralHi := (31563824063796452753/20000000000000000000)
  directionLo := (82761044900489174029/50000000000000000000)
  directionHi := (165522089800978348059/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree012.table
  base := (3066727713893234589070959436567244651211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-5440668723078990388388713758044801600000000000000)
      constant := (24684201054320726370827797889040196904031604138176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree012.table
  base := (3064265091552420552364817809748585207357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-363232824710128832171873725601700000000000000)
      constant := (1648118099549947513109663845951711416363439644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82761044900489174029/50000000000000000000)
  centralHi := (165522089800978348059/100000000000000000000)
  directionLo := (6915287376346279423/4000000000000000000)
  directionHi := (21610273051082123197/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree013.table
  base := (9095247744018756653202085315693437197589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-5773826194805794446308338527261925600000000000000)
      constant := (26939581304517532013790761313852647941539946120656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree013.table
  base := (9086131719896226153927554293182739696723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-1156430401009947756934548303569100000000000000)
      constant := (5396296575136697517366862159257707717300625787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6915287376346279423/4000000000000000000)
  centralHi := (21610273051082123197/12500000000000000000)
  directionLo := (44985370649616901703/25000000000000000000)
  directionHi := (179941482598467606813/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree014.table
  base := (6318747412609547112150384430607362918549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-6106983666532598504227963296479049600000000000000)
      constant := (29461190103857675040221864838952089405135793196496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree014.table
  base := (6310267597888221439645529671254519584657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-1223162327889509017353475430333100000000000000)
      constant := (5901564917770383524007011035666546299036303433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44985370649616901703/25000000000000000000)
  centralHi := (179941482598467606813/100000000000000000000)
  directionLo := (466835253552848399/250000000000000000)
  directionHi := (186734101421139359601/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree015.table
  base := (774516558265153230863264089714634883963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-1288028227651880512429517613139234720000000000000)
      constant := (6446868011213026064811906138835733942683383515952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree015.table
  base := (3864676589956982430149729330545979472059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-429964751589690092590800852365700000000000000)
      constant := (2152406601686745106869575695151346847555948257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466835253552848399/250000000000000000)
  centralHi := (186734101421139359601/100000000000000000000)
  directionLo := (9664407910910282537/5000000000000000000)
  directionHi := (193288158218205650741/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree016.table
  base := (854406314003196440919267780941713777053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-6773298609986206620067212834913297600000000000000)
      constant := (35248169461417151127283781837506678279446361662624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree016.table
  base := (1701437174859872198765457659487428168039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-1356626181648631538191329683861100000000000000)
      constant := (7061087085508995712445706043418885128555761391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9664407910910282537/5000000000000000000)
  centralHi := (193288158218205650741/100000000000000000000)
  directionLo := (199627151412857265877/100000000000000000000)
  directionHi := (99813575706428632939/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree017.table
  base := (-209678786506961458188726244135975137291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-7106456081713010677986837604130421600000000000000)
      constant := (38494269284485935329753102329087287904218579805136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree017.table
  base := (-21655587727441583877631860661272918849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-284671621705638559722051362125020000000000000)
      constant := (1542296666388526678219249227875057417889479438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199627151412857265877/100000000000000000000)
  centralHi := (99813575706428632939/50000000000000000000)
  directionLo := (205770957754095076591/100000000000000000000)
  directionHi := (12860684859630942287/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree018.table
  base := (-956345594255606208137904484489468176513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-7439613553439814735906462373347545600000000000000)
      constant := (41965888016437566797484220052424985360814530857696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree018.table
  base := (-1919097003406060358683645003107254733287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-496696678469251353009727979129700000000000000)
      constant := (2802352266850234003399821518476608986668500699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205770957754095076591/100000000000000000000)
  centralHi := (12860684859630942287/6250000000000000000)
  directionLo := (211736568709477581279/100000000000000000000)
  directionHi := (1323353554434234883/625000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree019.table
  base := (-1712403756416334915092346317499956338673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-7772771025166618793826087142564669600000000000000)
      constant := (45657456081085541003291979505261164519056610696416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree019.table
  base := (-1715383303455442637855544517769602360633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-1556821962287315319448111064153100000000000000)
      constant := (9146692303012443814566861318423521821000882846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211736568709477581279/100000000000000000000)
  centralHi := (1323353554434234883/625000000000000000)
  directionLo := (5438466121222110087/2500000000000000000)
  directionHi := (217538644848884403481/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree020.table
  base := (-2383351063320026484419189035793924380757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-8105928496893422851745711911781793600000000000000)
      constant := (49564289437900624085392282451895223411048337026144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree020.table
  base := (-4772237903594727895803423693642584119739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-1623553889166876579867038190917100000000000000)
      constant := (9929451916199963771465028022585129601071561309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5438466121222110087/2500000000000000000)
  centralHi := (217538644848884403481/100000000000000000000)
  directionLo := (4463798807137920317/2000000000000000000)
  directionHi := (223189940356896015851/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree021.table
  base := (-5955996575723260370328775429871925332411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-8439085968620226909665336680998917600000000000000)
      constant := (53682395701819996815109378727962286198002865000656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree021.table
  base := (-186285371753921064339827850291658310453/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-563428605348812613428655105893700000000000000)
      constant := (3584845397614407522740971186564956043872616992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4463798807137920317/2000000000000000000)
  centralHi := (223189940356896015851/100000000000000000000)
  directionLo := (28587704128682158857/12500000000000000000)
  directionHi := (228701633029457270857/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree022.table
  base := (-1401569858664903906437064919995142138599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-1754448688069406193516992290043208320000000000000)
      constant := (11601668107443979328723969022470098870214667788304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree022.table
  base := (-3506303336336117295286402519790162934007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-1757017742925999100704892444445100000000000000)
      constant := (11621257425640075815791670522723480195694072834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28587704128682158857/12500000000000000000)
  centralHi := (228701633029457270857/100000000000000000000)
  directionLo := (57149312565644759/24414062500000000)
  directionHi := (46816716853776186573/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree023.table
  base := (-3967691606894249457911143014450304506357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-9105400912073835025504586219433165600000000000000)
      constant := (62539150776610781016322147094026961049832745781344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree023.table
  base := (-1984946204369317318012283981025974878587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-1823749669805560361123819571209100000000000000)
      constant := (12529020256066036430160269593980630182933545588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57149312565644759/24414062500000000)
  centralHi := (46816716853776186573/20000000000000000000)
  directionLo := (239344546413725543619/100000000000000000000)
  directionHi := (11967227320686277181/5000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree024.table
  base := (-2187502555692465531558375174205288743093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-9438558383800639083424210988650289600000000000000)
      constant := (67272240912320990536658492157177333325056354386112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree024.table
  base := (-4377038886567772589793474997707237165251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-630160532228373873847582232657700000000000000)
      constant := (4492435652794004450014935399500146904699818254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239344546413725543619/100000000000000000000)
  centralHi := (11967227320686277181/5000000000000000000)
  directionLo := (48898465976681829247/20000000000000000000)
  directionHi := (61123082470852286559/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree025.table
  base := (-9461686645197933141436542672512653903377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-9771715855527443141343835757867413600000000000000)
      constant := (72205355212452634955277182161259596032434752148592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree025.table
  base := (-473272065106936016730442920077781584687/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-391442704712936576392334764947420000000000000)
      constant := (2893133169919904508534271578221464509137341988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48898465976681829247/20000000000000000000)
  centralHi := (61123082470852286559/25000000000000000000)
  directionLo := (249533939266071582347/100000000000000000000)
  directionHi := (62383484816517895587/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree026.table
  base := (-10079120244624059881104821953913635980313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-10104873327254247199263460527084537600000000000000)
      constant := (77336520822549728244652234540240161349828595953648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree026.table
  base := (-10082582490676815379570515406528027581923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2023945450444244142380600951501100000000000000)
      constant := (15493701897925208961512354093497829916635735413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533939266071582347/100000000000000000000)
  centralHi := (62383484816517895587/25000000000000000000)
  directionLo := (254475685124275166203/100000000000000000000)
  directionHi := (63618921281068791551/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree027.table
  base := (-10609941476201857775864960966537909792491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-10438030798981051257183085296301661600000000000000)
      constant := (82664008966059916557444757303007582213905160144336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree027.table
  base := (-5306565509947282830125382036051907789881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-696892459107935134266509359421700000000000000)
      constant := (5520356317451739036221718158267473996987259274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254475685124275166203/100000000000000000000)
  centralHi := (63618921281068791551/25000000000000000000)
  directionLo := (129661638306492739181/50000000000000000000)
  directionHi := (259323276612985478363/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree028.table
  base := (-1382605911560979828928500272188465078391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-10771188270707855315102710065518785600000000000000)
      constant := (88186302363303436866144934025551811633841304565888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree028.table
  base := (-11063782994615853190208590789767958959849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2157409304203366663218455205029100000000000000)
      constant := (17667463217309792281056601381425817469950610719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129661638306492739181/50000000000000000000)
  centralHi := (259323276612985478363/100000000000000000000)
  directionLo := (264081898787328324521/100000000000000000000)
  directionHi := (132040949393664162261/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree029.table
  base := (-5718861588862713029422159172011556970551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-11104345742434659373022334834735909600000000000000)
      constant := (93902067583055749723215747975793671842003834140192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree029.table
  base := (-5720211500257129732159101830787186625093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2224141231082927923637382331793100000000000000)
      constant := (18812617715021509759845746865985932260012311366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081898787328324521/100000000000000000000)
  centralHi := (132040949393664162261/50000000000000000000)
  directionLo := (268756277584257483033/100000000000000000000)
  directionHi := (134378138792128741517/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree030.table
  base := (-734109217651590690462980054523624772553/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-11437503214161463430941959603953033600000000000000)
      constant := (99810131404222861478435807253565332734384117387008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree030.table
  base := (-2937057114840058379233541544448881890501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-763624385987496394685436486185700000000000000)
      constant := (6665432517014022014264319579164198236679813508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268756277584257483033/100000000000000000000)
  centralHi := (134378138792128741517/50000000000000000000)
  directionLo := (136675367399151520703/50000000000000000000)
  directionHi := (273350734798303041407/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree031.table
  base := (-2997370276958274120546092449614600169617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-11770660685888267488861584373170157600000000000000)
      constant := (105909460496685986530389974234715237685770855342528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree031.table
  base := (-5995879665553475022197698095741417735743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2357605084842050444475236585321100000000000000)
      constant := (21218295844548345547100036631870715237494151666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136675367399151520703/50000000000000000000)
  centralHi := (273350734798303041407/100000000000000000000)
  directionLo := (277869234872444886367/100000000000000000000)
  directionHi := (8683413589763902699/3125000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree032.table
  base := (-3043236226863774804340875869955284695139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-12103818157615071546781209142387281600000000000000)
      constant := (112199143885002250695176708536779276561517970016576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree032.table
  base := (-6087517764931468350467589758412347715909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2424337011721611704894163712085100000000000000)
      constant := (22478430216057158481622070605016380392953849158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277869234872444886367/100000000000000000000)
  centralHi := (8683413589763902699/3125000000000000000)
  directionLo := (282315424945970108373/100000000000000000000)
  directionHi := (141157712472985054187/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree033.table
  base := (-3074921673801088047342776083385385838017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-12436975629341875604700833911604405600000000000000)
      constant := (118678377766858260128656830424980246216822249928128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree033.table
  base := (-12301603943521010222373738589340894721043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-830356312867057655104363612949700000000000000)
      constant := (7925513248937231881290544328417497649133666711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282315424945970108373/100000000000000000000)
  centralHi := (141157712472985054187/50000000000000000000)
  directionLo := (286692669310272775609/100000000000000000000)
  directionHi := (28669266931027277561/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree034.table
  base := (-3093209850083294078295484893961091763597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-12770133101068679662620458680821529600000000000000)
      constant := (125346452337331168306057902547039714016989339654848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree034.table
  base := (-6187298298783640565472937168918323187523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2557800865480734225732017965613100000000000000)
      constant := (25112482339947677685565453089240089190610538026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286692669310272775609/100000000000000000000)
  centralHi := (28669266931027277561/10000000000000000000)
  directionLo := (291004079198342443877/100000000000000000000)
  directionHi := (145502039599171221939/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree035.table
  base := (-6197585821903349189210920607727923714613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-13103290572795483720540083450038653600000000000000)
      constant := (132202740330168765012219457254810911988823108812896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree035.table
  base := (-12396781238110414066176348985193931081939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2624532792360295486150945092377100000000000000)
      constant := (26486132425591900600672931979689236540743509509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291004079198342443877/100000000000000000000)
  centralHi := (145502039599171221939/50000000000000000000)
  directionLo := (147626269328921352967/50000000000000000000)
  directionHi := (59050507731568541187/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree036.table
  base := (-12369131802676899562835591900117563339571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-13436448044522287778459708219255777600000000000000)
      constant := (139246687034445741842954531969729228531895524040016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree036.table
  base := (-12370605401065457486055165138588946026897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-897088239746618915523290739713700000000000000)
      constant := (9299126320495811518567840409438319369235236669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147626269328921352967/50000000000000000000)
  centralHi := (59050507731568541187/20000000000000000000)
  directionLo := (4678761361238842169/1562500000000000000)
  directionHi := (299440727119285898817/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree037.table
  base := (-1229688646204130367989762035178263865199/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-2753921103249818367275866597694580320000000000000)
      constant := (29295560316556791539875593697138739948350046123808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree037.table
  base := (-6149117433706196729893645899351271421967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2757996646119418006988799345905100000000000000)
      constant := (29346123688316998744159460596525364333713558354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4678761361238842169/1562500000000000000)
  centralHi := (299440727119285898817/100000000000000000000)
  directionLo := (37946392395134296379/12500000000000000000)
  directionHi := (303571139161074371033/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree038.table
  base := (-6090177008910044698281343714286430562291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-14102762987975895894298957757690025600000000000000)
      constant := (153895649338216394334541380737014893022598221210272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree038.table
  base := (-12181587268054415400018352821812145262633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2824728572998979267407726472669100000000000000)
      constant := (30832279605084146184102430775585004781579603423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37946392395134296379/12500000000000000000)
  centralHi := (303571139161074371033/100000000000000000000)
  directionLo := (38455762735694544411/12500000000000000000)
  directionHi := (307646101885556355289/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree039.table
  base := (-12021234080814613009913964724296018792851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-14435920459702699952218582526907149600000000000000)
      constant := (161499845232324148858910178054503726260856861570896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree039.table
  base := (-1202236148898542580787208244331935941291/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30246000000000000000000000000000000000000000
      center := (184529)
      previous := (0)
      next := (163300)
      square := (4192890980928185389153828318800000000000000)
      linear := (-192764033325236035188443573295540000000000000)
      constant := (2157051309002014634197263271131196265519712414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38455762735694544411/12500000000000000000)
  centralHi := (307646101885556355289/100000000000000000000)
  directionLo := (311667790249816898957/100000000000000000000)
  directionHi := (155833895124908449479/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree040.table
  base := (-11821033238370272458178588940691144602277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-14769077931429504010138207296124273600000000000000)
      constant := (169290047928604435733643595380836562650053118322992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree040.table
  base := (-11822063433295213720458297569488816193761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-2958192426758101788245580726197100000000000000)
      constant := (33916525456837938091904380187453861898105257191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311667790249816898957/100000000000000000000)
  centralHi := (155833895124908449479/50000000000000000000)
  directionLo := (315638240637964527529/100000000000000000000)
  directionHi := (31563824063796452753/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree041.table
  base := (-11581087650838307660021629681963961015909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-15102235403156308068057832065341397600000000000000)
      constant := (177265954702955100453016134476136343936685069942064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree041.table
  base := (-11582028617376505960584581782969247499479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3024924353637663048664507852961100000000000000)
      constant := (35514486479464080297714766877481568210196137249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315638240637964527529/100000000000000000000)
  centralHi := (31563824063796452753/10000000000000000000)
  directionLo := (31955936291533587571/10000000000000000000)
  directionHi := (319559362915335875711/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree042.table
  base := (-1412822861646809612087360990192389755577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-15435392874883112125977456834558521600000000000000)
      constant := (185427296948308371740456088556178149274036606398336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree042.table
  base := (-11303442011810732627436021450545837119403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1030552093505741436361144993241700000000000000)
      constant := (12383199647326112409406726984558795305243268431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31955936291533587571/10000000000000000000)
  centralHi := (319559362915335875711/100000000000000000000)
  directionLo := (4042911889589163311/1250000000000000000)
  directionHi := (323432951167133064881/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree043.table
  base := (-686660712205897286645570691353434974723/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-15768550346609916183897081603775645600000000000000)
      constant := (193773836223296806110955835085163803814017367504128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree043.table
  base := (-10987355480665344583678185568223876085877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3158388207396785569502362106489100000000000000)
      constant := (38821815122359832705232348216258550965859846387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4042911889589163311/1250000000000000000)
  centralHi := (323432951167133064881/100000000000000000000)
  directionLo := (327260693292834698533/100000000000000000000)
  directionHi := (163630346646417349267/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree044.table
  base := (-10633987786528508493308022744081587198967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-16101707818336720241816706372992769600000000000000)
      constant := (202305360775772033781334881582539386007590250473232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree044.table
  base := (-664668945289846120612653546375429006869/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3225120134276346829921289233253100000000000000)
      constant := (40531092641394035638868075127776290582197765424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327260693292834698533/100000000000000000000)
  centralHi := (163630346646417349267/50000000000000000000)
  directionLo := (82761044900489174029/25000000000000000000)
  directionHi := (331044179601956696117/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree045.table
  base := (-5122831204157269662586944801217041012833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-16434865290063524299736331142209893600000000000000)
      constant := (211021682481332707328644807582557845769507313639136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree045.table
  base := (-10246314792255264787337370575927820242739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1097284020385302696780072120005700000000000000)
      constant := (14092464616561027123108577852136743574469058103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82761044900489174029/25000000000000000000)
  centralHi := (331044179601956696117/100000000000000000000)
  directionLo := (13391396421413760951/4000000000000000000)
  directionHi := (10462028454229500743/3125000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree046.table
  base := (-9822333224005561627419433135431815615559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-16768022761790328357655955911427017600000000000000)
      constant := (219922634145006092667762463621404469746509528488464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree046.table
  base := (-9822927988074279518679782621786969735199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3358583988035469350759143486781100000000000000)
      constant := (44060685287382779876937740562630746970083756569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13391396421413760951/4000000000000000000)
  centralHi := (10462028454229500743/3125000000000000000)
  directionLo := (84621075904581847989/25000000000000000000)
  directionHi := (338484303618327391957/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree047.table
  base := (-9364656324440465753782778409585544727381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-17101180233517132415575580680644141600000000000000)
      constant := (229008067121077661171785423576120401042251617801776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree047.table
  base := (-4682599188281939517102343837904302502597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3425315914915030611178070613545100000000000000)
      constant := (45880937207651823630177293007527939399519353414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84621075904581847989/25000000000000000000)
  centralHi := (338484303618327391957/100000000000000000000)
  directionLo := (21383981233570479847/6250000000000000000)
  directionHi := (342143699737127677553/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree048.table
  base := (-8873215201942393170682301575026174482019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-17434337705243936473495205449861265600000000000000)
      constant := (238277849211948918668307414950842871838577975980624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree048.table
  base := (-4436854527192579463990258012912340554379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1164015947264863957198999246769700000000000000)
      constant := (15912707718659265127679033425791053347592252766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21383981233570479847/6250000000000000000)
  centralHi := (342143699737127677553/100000000000000000000)
  directionLo := (6915287376346279423/2000000000000000000)
  directionHi := (345764368817313971151/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree049.table
  base := (-8348528943046647508364580305913522587433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-17767495176970740531414830219078389600000000000000)
      constant := (247731862811970816775398756920968202907426103101168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree049.table
  base := (-2038324888035261299101080417825313951/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3558779768674153132015924867073100000000000000)
      constant := (49632219598559624896078248405186906925238603776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6915287376346279423/2000000000000000000)
  centralHi := (345764368817313971151/100000000000000000000)
  directionLo := (174673757486250107643/50000000000000000000)
  directionHi := (349347514972500215287/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree050.table
  base := (-3895529735485366094768185845244803422481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-18100652648697544589334454988295513600000000000000)
      constant := (257370003266570157537481751601513116089308500502752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree050.table
  base := (-9739336276741685882568068025458334891/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-725102339110742878486970398767420000000000000)
      constant := (10312641118760308528364014462151476928692835360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174673757486250107643/50000000000000000000)
  centralHi := (349347514972500215287/100000000000000000000)
  directionLo := (176447140591231317733/50000000000000000000)
  directionHi := (352894281182462635467/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree051.table
  base := (-3600608976087809575108475579729773729093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-18433810120424348647254079757512637600000000000000)
      constant := (267192177420761749042263756954776294724257052905056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree051.table
  base := (-7201590747034391990116902374375486295557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1230747874144425217617926373533700000000000000)
      constant := (17843687500576610189843109609227019520752291489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176447140591231317733/50000000000000000000)
  centralHi := (352894281182462635467/100000000000000000000)
  directionLo := (178202876776100855249/50000000000000000000)
  directionHi := (356405753552201710499/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree052.table
  base := (-164484261673699657533898274104738086473/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-3753393518430230541034740905345952320000000000000)
      constant := (55439660466881192089412591524267337919335130376064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree052.table
  base := (-6579709708754623173670850155696239947027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3758975549312836913272706247365100000000000000)
      constant := (55535773726798058828127676452903417289843332037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178202876776100855249/50000000000000000000)
  centralHi := (356405753552201710499/100000000000000000000)
  directionLo := (2879063721575481709/800000000000000000)
  directionHi := (179941482598467606813/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree053.table
  base := (-5925843031436225744059114449099335456573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (260732945)
      previous := (0)
      next := (230865375)
      square := (5925952586378502016670744023904000000000000000)
      linear := (-360379718186376542699874137659375200000000000000)
      constant := (5422420832913257818343407196328119006968976349936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree053.table
  base := (-5926151655250227720814770253433067970987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3825707476192398173691633374129100000000000000)
      constant := (57577324490113630179294431588066295139224290797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2879063721575481709/800000000000000000)
  centralHi := (179941482598467606813/50000000000000000000)
  directionLo := (36332689979241039161/10000000000000000000)
  directionHi := (363326899792410391611/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree054.table
  base := (-5240926047725937194495392327723043407633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-19433282535604760821012954065164009600000000000000)
      constant := (297762117056470100106519771906198382022457293280368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree054.table
  base := (-5241206742042387094608159365337172710849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1297479801023986478036853500297700000000000000)
      constant := (19885233875870234713744015975829805937093830573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36332689979241039161/10000000000000000000)
  centralHi := (363326899792410391611/100000000000000000000)
  directionLo := (45842311853139214919/12500000000000000000)
  directionHi := (366738494825113719353/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree055.table
  base := (-4524878249111980946518408992697214661397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-19766440007331564878932578834381133600000000000000)
      constant := (308319682451293369272542812869910735168045451262512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree055.table
  base := (-565641684413765705754205070330866920399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-3959171329951520694529487627657100000000000000)
      constant := (61770893411122444558160794845053771189507342152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45842311853139214919/12500000000000000000)
  centralHi := (366738494825113719353/100000000000000000000)
  directionLo := (185059322286406111187/50000000000000000000)
  directionHi := (2960949156582497779/800000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree056.table
  base := (-944482549879282611992005623526521274947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-20099597479058368936852203603598257600000000000000)
      constant := (319060948091686683470747703097724114896937920893248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree056.table
  base := (-3778162209940902900162903913677545469097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-4025903256831081954948414754421100000000000000)
      constant := (63922889389677962278887694834049963439612538207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185059322286406111187/50000000000000000000)
  centralHi := (2960949156582497779/800000000000000000)
  directionLo := (466835253552848399/125000000000000000)
  directionHi := (373468202842278719201/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree057.table
  base := (-1500143699427082072920708160340490318727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-20432754950785172994771828372815381600000000000000)
      constant := (329985867419034131852029840018047398480406778084384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree057.table
  base := (-1500249126798532881980046837580297199871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1364211727903547738455780627061700000000000000)
      constant := (22037226749557974762196897211231446330892701734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466835253552848399/125000000000000000)
  centralHi := (373468202842278719201/100000000000000000000)
  directionLo := (376787985487949419617/100000000000000000000)
  directionHi := (188393992743974709809/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree058.table
  base := (-548033259971400843655822137559215705991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-20765912422511977052691453142032505600000000000000)
      constant := (341094398928688084352990681987747225818125640161344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree058.table
  base := (-2192324622352491700372682933891858857627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-4159367110590204475786269007949100000000000000)
      constant := (68337257684854074834653321337512060255488320637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376787985487949419617/100000000000000000000)
  centralHi := (188393992743974709809/50000000000000000000)
  directionLo := (190039386366282583353/50000000000000000000)
  directionHi := (380078772732565166707/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree059.table
  base := (-1353630456680673050857472743958970384899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-21099069894238781110611077911249629600000000000000)
      constant := (352386505615240162053353883740675519779541361793104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree059.table
  base := (-676902243999112360123722893657112059287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-4226099037469765736205196134713100000000000000)
      constant := (70599614295277426047347476651476240965964416194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190039386366282583353/50000000000000000000)
  centralHi := (380078772732565166707/100000000000000000000)
  directionLo := (23958831956781115699/6250000000000000000)
  directionHi := (76668262261699570237/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree060.table
  base := (-30307831249837076994184161757536032009/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-21432227365965585168530702680466753600000000000000)
      constant := (363862154479660788279237053942738543907369766522624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree060.table
  base := (-30317709521471506728522794940810126079/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1430943654783108998874707753825700000000000000)
      constant := (24299581159557464244278031934095762055412916528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23958831956781115699/6250000000000000000)
  centralHi := (76668262261699570237/20000000000000000000)
  directionLo := (386576316436411301481/100000000000000000000)
  directionHi := (193288158218205650741/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree061.table
  base := (103463132315294477343832333958605956593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-21765384837692389226450327449683877600000000000000)
      constant := (375521316091250114129129326450198957133384866829888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree061.table
  base := (82741804068101305390785111100293838187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-871912578245777651408610077648220000000000000)
      constant := (15046927869552752382710165083908529231144706003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386576316436411301481/100000000000000000000)
  centralHi := (193288158218205650741/50000000000000000000)
  directionLo := (77956894731221854283/20000000000000000000)
  directionHi := (48723059207013658927/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree062.table
  base := (335646790257796897065971679991778581069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-22098542309419193284369952218901001600000000000000)
      constant := (387363964198173160463465369265543813912385103402304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree062.table
  base := (1342456885252148128429570300902923222421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-4426294818108449517461977515005100000000000000)
      constant := (77607296651325621675544390267749864723678018349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77956894731221854283/20000000000000000000)
  centralHi := (48723059207013658927/12500000000000000000)
  directionLo := (392966440522846534143/100000000000000000000)
  directionHi := (767512579146184637/195312500000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree063.table
  base := (1150587613621293899642929607457785614307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-22431699781145997342289576988118125600000000000000)
      constant := (399390075381080469944715442990031068124259390012256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree063.table
  base := (2301056989096978436362690524750258554101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1497675581662670259293634880589700000000000000)
      constant := (26672236901619752760887448428300898160113669423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392966440522846534143/100000000000000000000)
  centralHi := (767512579146184637/195312500000000000)
  directionLo := (396122848180992486781/100000000000000000000)
  directionHi := (198061424090496243391/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree064.table
  base := (822381125424599701323103696923334077157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-22764857252872801400209201757335249600000000000000)
      constant := (411599628744955475206997898987825490596864138210112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree064.table
  base := (131576688431612675576089105660776732227/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-911951734373514407659966353706620000000000000)
      constant := (16492575465784636172503350858806898897822033815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396122848180992486781/100000000000000000000)
  centralHi := (198061424090496243391/50000000000000000000)
  directionLo := (79850860565142906351/20000000000000000000)
  directionHi := (99813575706428632939/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree065.table
  base := (4307552689716392707839142918355751434231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-23098014724599605458128826526552373600000000000000)
      constant := (423992605644892445876896934217842373653891253520624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree065.table
  base := (269215959491530708318271477984434900153/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-4626490598747133298718758895297100000000000000)
      constant := (84945792794255109597132110380766313231760663312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79850860565142906351/20000000000000000000)
  centralHi := (99813575706428632939/25000000000000000000)
  directionLo := (25147586691391816489/6250000000000000000)
  directionHi := (16094455482490762553/4000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree066.table
  base := (1338796587689127055613627585713480473949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-23431172196326409516048451295769497600000000000000)
      constant := (436568989442004042449476964892752853721716347992384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree066.table
  base := (33469362873796152180782053998477931143/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30246000000000000000000000000000000000000000
      center := (184529)
      previous := (0)
      next := (163300)
      square := (4192890980928185389153828318800000000000000)
      linear := (-312881501708446303942512401470740000000000000)
      constant := (5831030251528328148756541878711847416085618848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25147586691391816489/6250000000000000000)
  centralHi := (16094455482490762553/4000000000000000000)
  directionLo := (405444661171532560633/100000000000000000000)
  directionHi := (202722330585766280317/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree067.table
  base := (1286471987836464414506422750384119092007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-4752865933610642714793615212997324320000000000000)
      constant := (89865753057218728293260300867018958775143130706928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree067.table
  base := (1286455973896715664169146545953201836567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-951990890501251163911322629765020000000000000)
      constant := (18004371458968978000668403041842090814123208223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405444661171532560633/100000000000000000000)
  centralHi := (202722330585766280317/50000000000000000000)
  directionLo := (408504664289558122133/100000000000000000000)
  directionHi := (204252332144779061067/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree068.table
  base := (7539014950001792973517514877899447637711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-24097487139780017631887700834203745600000000000000)
      constant := (462271919922112048555462265575746901496906216530544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree068.table
  base := (1884735587371574823380523918027820423677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-4826686379385817079975540275589100000000000000)
      constant := (92615000709040518985534311225078816739207207252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408504664289558122133/100000000000000000000)
  centralHi := (204252332144779061067/50000000000000000000)
  directionLo := (205770957754095076591/50000000000000000000)
  directionHi := (411541915508190153183/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree069.table
  base := (4337549578964716899737703810210212657709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-24430644611506821689807325603420869600000000000000)
      constant := (475398441517757366581750157135541641951291154970272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree069.table
  base := (2168758335441310304183384852085523671507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1631139435421792780131489134117700000000000000)
      constant := (31748293883051074947577518095149657497936801444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205770957754095076591/50000000000000000000)
  centralHi := (411541915508190153183/100000000000000000000)
  directionLo := (207278457451549980743/50000000000000000000)
  directionHi := (414556914903099961487/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree070.table
  base := (1968113187886714531290489494096945112987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-4952760416646725149545390074527598720000000000000)
      constant := (97741663901975237986246061606535338822937920236848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree070.table
  base := (984050628419677748689435178284514205771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-992030046628987920162678905823420000000000000)
      constant := (19582299600541204151911732843106580250003248998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207278457451549980743/50000000000000000000)
  centralHi := (414556914903099961487/100000000000000000000)
  directionLo := (208775072247503846357/50000000000000000000)
  directionHi := (83510028899001538543/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree071.table
  base := (1379421708574974499058997559683693448057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31910240000000000000000000000000000000000000000
      center := (194631635)
      previous := (0)
      next := (172336125)
      square := (4423598409550149392726048355872000000000000000)
      linear := (-353478303590991969093613734392325600000000000000)
      constant := (7073261189684349191506938633848263010611141122944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree071.table
  base := (1103531960693040307573964391466016351187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1278000000000000000000000000000000000000000
      center := (7797)
      previous := (0)
      next := (6900)
      square := (177164407644852903767063168400000000000000)
      linear := (-14160231436688734820372737058820000000000000)
      constant := (283422106714693969502493778230113568896816986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208775072247503846357/50000000000000000000)
  centralHi := (83510028899001538543/20000000000000000000)
  directionLo := (105130517287330615701/25000000000000000000)
  directionHi := (84104413829864492561/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree072.table
  base := (490379407146946494429740034954335136451/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-5086023405337446772713239982214448320000000000000)
      constant := (103175621594058957884168526587795088865182737617520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree072.table
  base := (6129718097188569155233793870151423827997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1697871362301354040550416260881700000000000000)
      constant := (34451643202762361221812363105502999965101597262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105130517287330615701/25000000000000000000)
  centralHi := (84104413829864492561/20000000000000000000)
  directionLo := (423473137418955162559/100000000000000000000)
  directionHi := (1323353554434234883/312500000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree073.table
  base := (13512867282058610900500101186180639656987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-25763274498414037921485824680289365600000000000000)
      constant := (529738002498922564313064359769015703328136607212848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree073.table
  base := (13512822905618345110673063728642108459781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-5160346013783623382070175909409100000000000000)
      constant := (106131741672847856544644158481981063818711804189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423473137418955162559/100000000000000000000)
  centralHi := (1323353554434234883/312500000000000000)
  directionLo := (213201891167315295417/50000000000000000000)
  directionHi := (85280756466926118167/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree074.table
  base := (14795490342352896670038187452793795328113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-26096431970140841979405449449506489600000000000000)
      constant := (543781221338968801109347134878879645523959848497552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree074.table
  base := (14795450146821193854390605455174094711813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-5227077940663184642489103036173100000000000000)
      constant := (108945282734756076163887547521893193502980243997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213201891167315295417/50000000000000000000)
  centralHi := (85280756466926118167/20000000000000000000)
  directionLo := (85862884429328313397/20000000000000000000)
  directionHi := (214657211073320783493/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree075.table
  base := (251676998323825381038507865500438357501/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-26429589441867646037325074218723613600000000000000)
      constant := (558007758494036544613494617182027177532487695533056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree075.table
  base := (16107291489962335186018029457064941752991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1764603289180915300969343387645700000000000000)
      constant := (37265183864999583728750980324906693114130482893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85862884429328313397/20000000000000000000)
  centralHi := (214657211073320783493/50000000000000000000)
  directionLo := (432205461021642463937/100000000000000000000)
  directionHi := (216102730510821231969/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree076.table
  base := (1744835629555944018474789909257042989677/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-5352549382718890019048939797588147520000000000000)
      constant := (114483521721744766953402019662064373701570930413216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree076.table
  base := (17448323332795095220362210146081827795319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-5360541794422307163326957289701100000000000000)
      constant := (114682547182765552264243011925649186445245827711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432205461021642463937/100000000000000000000)
  centralHi := (216102730510821231969/50000000000000000000)
  directionLo := (435077289697768806961/100000000000000000000)
  directionHi := (217538644848884403481/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree077.table
  base := (9409277219435876924687229880921520319703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-27095904385321254153164323757157861600000000000000)
      constant := (587010766899842265379253202978731674885845712313824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree077.table
  base := (9409262297778651211614087554208545534173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-5427273721301868423745884416465100000000000000)
      constant := (117606268541688749437522868671238475004679789674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435077289697768806961/100000000000000000000)
  centralHi := (217538644848884403481/50000000000000000000)
  directionLo := (437930286101089362979/100000000000000000000)
  directionHi := (21896514305054468149/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree078.table
  base := (20217903465479909409043740713726969253211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-27429061857048058211083948526374985600000000000000)
      constant := (601787229095057725341627556042767063371732344842544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree078.table
  base := (20217876450415078980853269433127653375063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1831335216060476561388270514409700000000000000)
      constant := (40188904939189449167853304440277789501991077749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437930286101089362979/100000000000000000000)
  centralHi := (21896514305054468149/5000000000000000000)
  directionLo := (88152963185228827187/20000000000000000000)
  directionHi := (1721737562211500531/390625000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree079.table
  base := (21646386531373888821552729156347672912559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-27762219328774862269003573295592109600000000000000)
      constant := (616746991378145758763402856807354348314176922599536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree079.table
  base := (21646362080079978443097636681165266085551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-5560737575060990944583738669993100000000000000)
      constant := (123563885247420786935357750727650686957035363319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88152963185228827187/20000000000000000000)
  centralHi := (1721737562211500531/390625000000000000)
  directionLo := (221790616591546464469/50000000000000000000)
  directionHi := (443581233183092928939/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree080.table
  base := (721999643440869397142777214652340662737/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-28095376800501666326923198064809233600000000000000)
      constant := (631890050340142903435467874776995615055323096347136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree080.table
  base := (23103966462429224539173603476802110690333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-5627469501940552205002665796757100000000000000)
      constant := (126597779149707379496287014938307034959909717877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221790616591546464469/50000000000000000000)
  centralHi := (443581233183092928939/100000000000000000000)
  directionLo := (446379880713792031701/100000000000000000000)
  directionHi := (223189940356896015851/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree081.table
  base := (2459069620039249487024112139567347999273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-5685706854445694076968564566805271520000000000000)
      constant := (129443280587150866129783995384519590100648561828384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree081.table
  base := (24590676178307224978230846014104617514079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1898067142940037821807197641173700000000000000)
      constant := (43222798638538151706568039204017004130665416717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446379880713792031701/100000000000000000000)
  centralHi := (223189940356896015851/50000000000000000000)
  directionLo := (17966443627157153929/4000000000000000000)
  directionHi := (224580545339464424113/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree082.table
  base := (26106497354374294039795412967369038294441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-28761691743955274442762447603243481600000000000000)
      constant := (662726046444448255639617741093252648781868101128464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree082.table
  base := (6526619809999009886228279652700411287039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-5760933355699674725840520050285100000000000000)
      constant := (132775735001271238575978561238523659838726689564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17966443627157153929/4000000000000000000)
  centralHi := (224580545339464424113/50000000000000000000)
  directionLo := (112981296254543467329/25000000000000000000)
  directionHi := (451925185018173869317/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree083.table
  base := (6912845331090472779871791970134626759943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-29094849215682078500682072372460605600000000000000)
      constant := (678418978435729923662947683463134069306053779863488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree083.table
  base := (27651364938117518209367002432765950915573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-5827665282579235986259447177049100000000000000)
      constant := (135919795920803952576405926058639458427088631437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112981296254543467329/25000000000000000000)
  centralHi := (451925185018173869317/100000000000000000000)
  directionLo := (90934495177030905107/20000000000000000000)
  directionHi := (14208514871411078923/3125000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree084.table
  base := (29225338526006644138800707176798360001243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-29428006687408882558601697141677729600000000000000)
      constant := (694295196738143390315341883533034936904647057441072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree084.table
  base := (14612661852487156796509531476458711595309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-1964799069819599082226124767937700000000000000)
      constant := (46366859413378578722589237973779770190911716014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90934495177030905107/20000000000000000000)
  centralHi := (14208514871411078923/3125000000000000000)
  directionLo := (28587704128682158857/6250000000000000000)
  directionHi := (457403266058914541713/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree085.table
  base := (30828360396160114570480631306443157101261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-29761164159135686616521321910894853600000000000000)
      constant := (710354699411598590610687580282373604670158493969744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree085.table
  base := (6165669398510875038683703655995507915379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-1192225827267671701419460286115420000000000000)
      constant := (28463616314290366126163647060599560198612829851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28587704128682158857/6250000000000000000)
  centralHi := (457403266058914541713/100000000000000000000)
  directionLo := (115029462333348511471/25000000000000000000)
  directionHi := (92023569866678809177/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree086.table
  base := (8115109820956399091142178249581474281617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-30094321630862490674440946680111977600000000000000)
      constant := (726597484722665022531213078653552466826198420049472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree086.table
  base := (32460427163616909192716899186413655921531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-6027861063217919767516228557341100000000000000)
      constant := (145572305568258258390835523003231001155503939939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115029462333348511471/25000000000000000000)
  centralHi := (92023569866678809177/20000000000000000000)
  directionLo := (18512660435453944497/4000000000000000000)
  directionHi := (231408255443174306213/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree087.table
  base := (682431367055853549484172601971243874417/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-6085495820517858946472114289865820320000000000000)
      constant := (148604710224502474002125687119978474539313519435680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree087.table
  base := (34121557394449841745903999841537038947283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2031530996699160342645051894701700000000000000)
      constant := (49621083306990008789848436331235464639999760809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18512660435453944497/4000000000000000000)
  centralHi := (231408255443174306213/50000000000000000000)
  directionLo := (465499527629018527793/100000000000000000000)
  directionHi := (232749763814509263897/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree088.table
  base := (7162348298939411012905184786396717245527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-6152127314863219758056039243709245120000000000000)
      constant := (151926579445442619916317925652682179635870029025008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree088.table
  base := (7162346317608389514502618479056938740131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-1232264983395408457670816562173820000000000000)
      constant := (30438182870594366457439619659718894253701003339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465499527629018527793/100000000000000000000)
  centralHi := (232749763814509263897/50000000000000000000)
  directionLo := (468167168537761865729/100000000000000000000)
  directionHi := (46816716853776186573/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree089.table
  base := (18765476625692103748791753479865033855177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-31093794046042902848199820987763349600000000000000)
      constant := (776425521800152963971979121109419215025560891037216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree089.table
  base := (75061888593098233597349845446341122697/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-1245611368771320709754601987526620000000000000)
      constant := (31111059723420087344585263345504285039564019300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468167168537761865729/100000000000000000000)
  centralHi := (46816716853776186573/10000000000000000000)
  directionLo := (58852461871096945191/12500000000000000000)
  directionHi := (470819694968775561529/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree090.table
  base := (3927919874557696580438908325409541943279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-6285390303553941381223889151396094720000000000000)
      constant := (158680284747264571924543425483473602760141409732832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree090.table
  base := (4909898831506950797884470024851551540179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2098262923578721603063979021465700000000000000)
      constant := (52985467497501123443562867211899640111537016136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58852461871096945191/12500000000000000000)
  centralHi := (470819694968775561529/100000000000000000000)
  directionLo := (473457360956946791293/100000000000000000000)
  directionHi := (236728680478473395647/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree091.table
  base := (8211294723791037247959303998374158481167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-6352021797899302192807814105239519520000000000000)
      constant := (162112120409657997973846930491937588744217728595568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree091.table
  base := (20528233152369609740002856281330064525703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-6361520697615726069610864191161100000000000000)
      constant := (162394225781833549861791940921203427394933238814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473457360956946791293/100000000000000000000)
  centralHi := (236728680478473395647/50000000000000000000)
  directionLo := (119020103374950470983/25000000000000000000)
  directionHi := (476080413499801883933/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree092.table
  base := (42862773976852076603083976553715406495601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-32093266461223315021958695295414721600000000000000)
      constant := (827903055853668115091530045273804122942102526665104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree092.table
  base := (42862767367645649487746033223564528823997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-6428252624495287330029791317925100000000000000)
      constant := (165868768308743745380022956769941099108215919893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119020103374950470983/25000000000000000000)
  centralHi := (476080413499801883933/100000000000000000000)
  directionLo := (239344546413725543619/50000000000000000000)
  directionHi := (478689092827451087239/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree093.table
  base := (44698096338857578630463388953017154655117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-32426423932950119079878320064631845600000000000000)
      constant := (845428784363926121460561936799984692692049494956368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree093.table
  base := (44698090367363021435672031077013738463211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2164994850458282863482906148229700000000000000)
      constant := (56460009971882911176613125857063778766779139953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239344546413725543619/50000000000000000000)
  centralHi := (478689092827451087239/100000000000000000000)
  directionLo := (60160454082420525723/12500000000000000000)
  directionHi := (96256726531872841157/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree094.table
  base := (23281218797347858005591246407454804149723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-32759581404676923137797944833848969600000000000000)
      constant := (863137786874391473597126349747337045271903327461984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree094.table
  base := (1455076006248878770647546321490428316843/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-6561716478254409850867645571453100000000000000)
      constant := (172928010461726440509192733291769775753819202144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60160454082420525723/12500000000000000000)
  centralHi := (96256726531872841157/20000000000000000000)
  directionLo := (483864260448753916871/100000000000000000000)
  directionHi := (60483032556094239609/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree095.table
  base := (48455794964811011307660644619113814514523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-33092738876403727195717569603066093600000000000000)
      constant := (881030062755320566614954022301846702275164778150192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree095.table
  base := (24227895045825973035414208612787834337029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-6628448405133971111286572698217100000000000000)
      constant := (176512709821132470175537082955531642512073337402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483864260448753916871/100000000000000000000)
  centralHi := (60483032556094239609/12500000000000000000)
  directionLo := (3800243731369453063/781250000000000000)
  directionHi := (97286239523057998413/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree096.table
  base := (12594541491289967224999565844264200959157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-33425896348130531253637194372283217600000000000000)
      constant := (899105611443921766636517949186275578638824013922112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree096.table
  base := (2518908078180248805756878338655512565177/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30246000000000000000000000000000000000000000
      center := (184529)
      previous := (0)
      next := (163300)
      square := (4192890980928185389153828318800000000000000)
      linear := (-446345355467568824780366654998740000000000000)
      constant := (12008941858760344594508778257192189266092687084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3800243731369453063/781250000000000000)
  centralHi := (97286239523057998413/20000000000000000000)
  directionLo := (48898465976681829247/10000000000000000000)
  directionHi := (488984659766818292471/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree097.table
  base := (52329548375757026629093260525683162889851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-33759053819857335311556819141500341600000000000000)
      constant := (917364432437229209826903083003730365406597096717104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree097.table
  base := (52329544400572701282612648136957614752581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-6761912258893093632124426951745100000000000000)
      constant := (183792264542040836369470300884772330023709847389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48898465976681829247/10000000000000000000)
  centralHi := (488984659766818292471/100000000000000000000)
  directionLo := (245762428455356446571/50000000000000000000)
  directionHi := (491524856910712893143/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree098.table
  base := (6788742526571939663270028861644412846817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-34092211291584139369476443910717465600000000000000)
      constant := (935806525285736381690898923882743953788537578505344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree098.table
  base := (54309936622820278564179238875158470646941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-6828644185772654892543354078509100000000000000)
      constant := (187487119713220882438574266564430864654781066229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245762428455356446571/50000000000000000000)
  centralHi := (491524856910712893143/100000000000000000000)
  directionLo := (494051993655447689653/100000000000000000000)
  directionHi := (247025996827723844827/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree099.table
  base := (56319339702441693816408655126087384134793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-34425368763310943427396068679934589600000000000000)
      constant := (954431889587708266076636733365048916464865402560272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree099.table
  base := (3519958528816515111133087685181362314167/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2298458704217405384320760401757700000000000000)
      constant := (63739564438224895182581887849116263876434360656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494051993655447689653/100000000000000000000)
  centralHi := (247025996827723844827/50000000000000000000)
  directionLo := (19862650776117401767/4000000000000000000)
  directionHi := (31035391837683440261/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree100.table
  base := (14589436315151332068683413627148890753979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-34758526235037747485315693449151713600000000000000)
      constant := (973240524984099566189850948805182561999288323996864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree100.table
  base := (58357742334079626897434999623200293247003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-6962108039531777413381208332037100000000000000)
      constant := (194986985274663650304042252114614974104323279107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19862650776117401767/4000000000000000000)
  centralHi := (31035391837683440261/6250000000000000000)
  directionLo := (249533939266071582347/50000000000000000000)
  directionHi := (99813575706428632939/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree101.table
  base := (60425155470699103691693769395764949094751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-35091683706764551543235318218368837600000000000000)
      constant := (992232431154014272836188573656286092990329138766704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree101.table
  base := (60425152828693150458101196749456588956773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-7028839966411338673800135458801100000000000000)
      constant := (198791995529073518009986050728385195984379834237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533939266071582347/50000000000000000000)
  centralHi := (99813575706428632939/20000000000000000000)
  directionLo := (125389252643617682661/25000000000000000000)
  directionHi := (100311402114894146129/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree102.table
  base := (31260784533416213532840496643433605621559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-35424841178491355601154942987585961600000000000000)
      constant := (1011407607810648790297041821617504920768180015471072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree102.table
  base := (62521566681907662791559104050238463332461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2365190631096966644739687528521700000000000000)
      constant := (67544574673534456994087919135009156280976807703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125389252643617682661/25000000000000000000)
  centralHi := (100311402114894146129/20000000000000000000)
  directionLo := (12600846259533163899/2500000000000000000)
  directionHi := (504033850381326555961/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree103.table
  base := (32323492458795903639000730778578225224103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-35757998650218159659074567756803085600000000000000)
      constant := (1030766054697667018682479425771246669139587563309024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree103.table
  base := (6464698276493038760035654627040163843911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-1432460764034092238927597942465820000000000000)
      constant := (41302434139608201950607252881078230386868796318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12600846259533163899/2500000000000000000)
  centralHi := (504033850381326555961/100000000000000000000)
  directionLo := (126624644571083403003/25000000000000000000)
  directionHi := (506498578284333612013/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree104.table
  base := (33400701005872208544295174416705365489267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-36091156121944963716994192526020209600000000000000)
      constant := (1050307771585961314279427442145666367153113228995936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree104.table
  base := (6680140006890181259329941737855094849267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-1445807149410004491011383367818620000000000000)
      constant := (42085467103123097421832877266587575596432789046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126624644571083403003/25000000000000000000)
  centralHi := (506498578284333612013/100000000000000000000)
  directionLo := (508951370248550332407/100000000000000000000)
  directionHi := (63618921281068791551/12500000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree105.table
  base := (34492409722731607098096595556897804147491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-36424313593671767774913817295237333600000000000000)
      constant := (1070032758270758178435791276784437742093635951551328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree105.table
  base := (17246204423035957664510477056271655666937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2431922557976527905158614655285700000000000000)
      constant := (71459739477472856336356035390786484994604353004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508951370248550332407/100000000000000000000)
  centralHi := (63618921281068791551/12500000000000000000)
  directionLo := (511392398019077620791/100000000000000000000)
  directionHi := (63924049752384702599/12500000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree106.table
  base := (71197236410911415207492185239970251862931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (260732945)
      previous := (0)
      next := (230865375)
      square := (5925952586378502016670744023904000000000000000)
      linear := (-693537189913180600619498906876499200000000000000)
      constant := (20564924803189281605949406654201270853615597825008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree106.table
  base := (71197234828765130712839259228256590589163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-7362499600809144975894771092621100000000000000)
      constant := (218367819411887772560279745926191373258439736147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511392398019077620791/100000000000000000000)
  centralHi := (63924049752384702599/12500000000000000000)
  directionLo := (256910914630698613947/50000000000000000000)
  directionHi := (102764365852279445579/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree107.table
  base := (73438652186041450970858686114722689675343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-37090628537125375890753066833671581600000000000000)
      constant := (1110032540317193504634389297973274519357998592207472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree107.table
  base := (458991567240494714601067446143867766713/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-1485846305537741247262739643877020000000000000)
      constant := (44478627684268883378754666781730776374656067104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256910914630698613947/50000000000000000000)
  centralHi := (102764365852279445579/20000000000000000000)
  directionLo := (258119913847883007819/50000000000000000000)
  directionHi := (516239827695766015639/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree108.table
  base := (18927266531369751764994877173538542966181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-37423786008852179948672691602888705600000000000000)
      constant := (1130307335369025167224431788731861174970552591653696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree108.table
  base := (15141812967501078678820069584874120356357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30246000000000000000000000000000000000000000
      center := (184529)
      previous := (0)
      next := (163300)
      square := (4192890980928185389153828318800000000000000)
      linear := (-499730896971217833115508356409940000000000000)
      constant := (15097011695438721609068021374898371322149186911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258119913847883007819/50000000000000000000)
  centralHi := (516239827695766015639/100000000000000000000)
  directionLo := (20745862129038838269/4000000000000000000)
  directionHi := (259323276612985478363/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree109.table
  base := (78008477652376569739206158137014587384107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-37756943480578984006592316372105829600000000000000)
      constant := (1150765399593834780377820360763663646180187568545328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree109.table
  base := (78008476490438605559746999937993513259989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-7562695381447828757151552472913100000000000000)
      constant := (230553930416491433847892445206742727703092440941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20745862129038838269/4000000000000000000)
  centralHi := (259323276612985478363/50000000000000000000)
  directionLo := (104208432412546282321/20000000000000000000)
  directionHi := (260521081031365705803/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree110.table
  base := (20084221562783308553307830326600727092163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-38090100952305788064511941141322953600000000000000)
      constant := (1171406732874806408919283622693410913933466025955008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree110.table
  base := (40168442601491423725931529175090628651413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-7629427308327390017570479599677100000000000000)
      constant := (234689403352743153374125881252870373462571912794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104208432412546282321/20000000000000000000)
  centralHi := (260521081031365705803/50000000000000000000)
  directionLo := (6542835085525227189/1250000000000000000)
  directionHi := (523426806842018175121/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree111.table
  base := (1292098304076383557336999026176716277671/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-38423258424032592122431565910540077600000000000000)
      constant := (1192231335107526262492960101123092087764437221272576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree111.table
  base := (16538858103091645665142434342134840902547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30246000000000000000000000000000000000000000
      center := (184529)
      previous := (0)
      next := (163300)
      square := (4192890980928185389153828318800000000000000)
      linear := (-513077282347130085199293781762740000000000000)
      constant := (15924106281298717716768179015527445198969218281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6542835085525227189/1250000000000000000)
  centralHi := (523426806842018175121/100000000000000000000)
  directionLo := (525800636738542895373/100000000000000000000)
  directionHi := (262900318369271447687/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree112.table
  base := (21270173217426999151486459363751943292471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-38756415895759396180351190679757201600000000000000)
      constant := (1213239206198665343848850956246833930630387570406336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree112.table
  base := (85080692016998112782869727113930264864413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-7762891162086512538408333853205100000000000000)
      constant := (243070502998063662598691730883955102186633553397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525800636738542895373/100000000000000000000)
  centralHi := (262900318369271447687/50000000000000000000)
  directionLo := (264081898787328324521/50000000000000000000)
  directionHi := (528163797574656649043/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree113.table
  base := (17499218021877306572267468713930917338049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-7817914673497240047654163089794865120000000000000)
      constant := (246886069212960424329828706025498967936308863524496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree113.table
  base := (21874022335090818852405106271965002806521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-7829623088966073798827260979969100000000000000)
      constant := (247316129671830567497838168784251420849316204996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081898787328324521/50000000000000000000)
  centralHi := (528163797574656649043/100000000000000000000)
  directionLo := (530516431924882629107/100000000000000000000)
  directionHi := (132629107981220657277/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree114.table
  base := (22485120712701094651849117919415148330267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-39422730839213004296190440218191449600000000000000)
      constant := (1255804754631370329089168508705102595317065506247872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree114.table
  base := (5621280134831709156118091509177478051587/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2632118338615211686415396035577700000000000000)
      constant := (83866158075296423633892117755066456009186403216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530516431924882629107/100000000000000000000)
  centralHi := (132629107981220657277/25000000000000000000)
  directionLo := (266429339608147494313/50000000000000000000)
  directionHi := (532858679216294988627/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree115.table
  base := (18482774159955271614610428688119632911041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-7951177662187961670822012997481714720000000000000)
      constant := (255472486366343715453903348699021441382812840414864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree115.table
  base := (577586688590218042144521693653607559501/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90738000000000000000000000000000000000000000
      center := (553587)
      previous := (0)
      next := (489900)
      square := (12578672942784556167461484956400000000000000)
      linear := (-1592617388545039263933023046699420000000000000)
      constant := (51183507329385743024879600466653156683744027808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266429339608147494313/50000000000000000000)
  centralHi := (532858679216294988627/100000000000000000000)
  directionLo := (535190675824943819543/100000000000000000000)
  directionHi := (66898834478117977443/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree116.table
  base := (23729063423335565715617090385356004775087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-40089045782666612412029689756625697600000000000000)
      constant := (1299103377606269890331624128604822603377922490220992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree116.table
  base := (5932265820593729992355590628413722085303/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8029818869604757580084042360261100000000000000)
      constant := (260273316923051051580156874613503634516609788912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535190675824943819543/100000000000000000000)
  centralHi := (66898834478117977443/12500000000000000000)
  directionLo := (268756277584257483033/50000000000000000000)
  directionHi := (537512555168514966067/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree117.table
  base := (48723815648225674294582574221852454334607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-40422203254393416469949314525842821600000000000000)
      constant := (1321027591901770536050076939281735209461170165394656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree117.table
  base := (97447630788096415728498885528418023842309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2698850265494772946834323162341700000000000000)
      constant := (88221938347873848583903372410429165774567239007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268756277584257483033/50000000000000000000)
  centralHi := (537512555168514966067/100000000000000000000)
  directionLo := (539824447795402820437/100000000000000000000)
  directionHi := (269912223897701410219/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree118.table
  base := (6250500212437440922056116512887999024043/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-40755360726120220527868939295059945600000000000000)
      constant := (1343135074670618657075208157239252909828584689476352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree118.table
  base := (25002000735175980923281241788554531789551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8163282723363880100921896613789100000000000000)
      constant := (269095030999134431649996228232305522211040557276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539824447795402820437/100000000000000000000)
  centralHi := (269912223897701410219/50000000000000000000)
  directionLo := (542126481470364372243/100000000000000000000)
  directionHi := (135531620367591093061/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree119.table
  base := (51298684906589250598260638033866863448371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-41088518197847024585788564064277069600000000000000)
      constant := (1365425825870264218808811013622288955092723396310368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree119.table
  base := (25649342350010642980722542508866041459419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8230014650243441361340823740553100000000000000)
      constant := (273560964781093019657672556989525873739889522444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542126481470364372243/100000000000000000000)
  centralHi := (135531620367591093061/25000000000000000000)
  directionLo := (272209390628456766089/50000000000000000000)
  directionHi := (544418781256913532179/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree120.table
  base := (105215730371113300096866018534010534044347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-41421675669573828643708188833494193600000000000000)
      constant := (1387899845462672692887915583134496874557571312234288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree120.table
  base := (105215729998712427535252577411597473779033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2765582192374334207253250289105700000000000000)
      constant := (92687872127300847406597019760479588595960316059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272209390628456766089/50000000000000000000)
  centralHi := (544418781256913532179/100000000000000000000)
  directionLo := (136675367399151520703/25000000000000000000)
  directionHi := (546701469596606082813/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree121.table
  base := (53931542461370891571350202535737962721527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-41754833141300632701627813602711317600000000000000)
      constant := (1410557133413845701973178101304352365914280712258016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree121.table
  base := (53931542293541164391390665142444337360003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8363478504002563882178677994081100000000000000)
      constant := (282602985794774383159032544466176214283371952214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136675367399151520703/25000000000000000000)
  centralHi := (546701469596606082813/100000000000000000000)
  directionLo := (137243666596339370291/25000000000000000000)
  directionHi := (109794933277071496233/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree122.table
  base := (110539433333925924748762406458371419871727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-42087990613027436759547438371928441600000000000000)
      constant := (1433397689693392572278780420242846812022457802269808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree122.table
  base := (110539433031403196655598591685800822542519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8430210430882125142597605120845100000000000000)
      constant := (287179073013640480509797864958267297517931544511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137243666596339370291/25000000000000000000)
  centralHi := (109794933277071496233/20000000000000000000)
  directionLo := (55123848904692811301/10000000000000000000)
  directionHi := (551238489046928113011/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree123.table
  base := (113244775484761084390456894275513858738183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-42421148084754240817467063141145565600000000000000)
      constant := (1456421514274147384225322289150102831000196768526832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree123.table
  base := (56622387606060875696675609403074906765171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2832314119253895467672177415869700000000000000)
      constant := (97263959344358940507546519673882503630019362066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55123848904692811301/10000000000000000000)
  centralHi := (551238489046928113011/100000000000000000000)
  directionLo := (17296657893865732553/3125000000000000000)
  directionHi := (553493052603703441697/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree124.table
  base := (11597911126806523061562262273196252387209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-8550861111296208975077337582072537920000000000000)
      constant := (295925721426365337389357801907143255007025052106272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree124.table
  base := (115979111022373334993221664816014878664961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8563674284641247663435459374373100000000000000)
      constant := (296441400848235063528627797374190179030150615609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17296657893865732553/3125000000000000000)
  centralHi := (553493052603703441697/100000000000000000000)
  directionLo := (111147693948977954547/20000000000000000000)
  directionHi := (8683413589763902699/1562500000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree125.table
  base := (927675317093973268095984553903894899231/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-43087463028207848933306312679579813600000000000000)
      constant := (1503018968244723556459459157662824807991202608719872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree125.table
  base := (118742440366634806308660791359190838595269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8630406211520808923854386501137100000000000000)
      constant := (301127641454781417137084792157812629156228759261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111147693948977954547/20000000000000000000)
  centralHi := (8683413589763902699/1562500000000000000)
  directionLo := (278987425446120019813/50000000000000000000)
  directionHi := (557974850892240039627/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree126.table
  base := (60767381679503299141266517786374020089691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-43420620499934652991225937448796937600000000000000)
      constant := (1526592597593434136642727620670106892793741430968928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree126.table
  base := (1898980674367507805749712125495712938149/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (922645)
      previous := (0)
      next := (816500)
      square := (20964454904640926945769141594000000000000000)
      linear := (-2899046046133456728091104542633700000000000000)
      constant := (101950199949614006692538291617689986672872148928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278987425446120019813/50000000000000000000)
  centralHi := (557974850892240039627/100000000000000000000)
  directionLo := (1400505760658545197/250000000000000000)
  directionHi := (560202304263418078801/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree127.table
  base := (12435607950444116968226527851923483181711/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453125408000000000000000000000000000000000000000
      center := (2763769217)
      previous := (0)
      next := (2447172975)
      square := (62815097415612121376709886653382400000000000000)
      linear := (-8750755594332291409829112443602812320000000000000)
      constant := (310069899032122642525543091817016621816493935013088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree127.table
  base := (124356079324706045845372463604606077219203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8763870065279931444692240754665100000000000000)
      constant := (310610276026954112056422901010777073117358020907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1400505760658545197/250000000000000000)
  centralHi := (560202304263418078801/100000000000000000000)
  directionLo := (112484187186620855349/20000000000000000000)
  directionHi := (281210467966552138373/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree128.table
  base := (31801597238974066232005853924828674101061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-44086935443388261107065186987231185600000000000000)
      constant := (1574289660930755732953189289244521697364284597715776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree128.table
  base := (31801597198491618294454010201512038455847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2767935)
      previous := (0)
      next := (2449500)
      square := (62893364713922780837307424782000000000000000)
      linear := (-8830601992159492705111167881429100000000000000)
      constant := (315406669986022394320518733608206398690813290172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell148.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112484187186620855349/20000000000000000000)
  centralHi := (281210467966552138373/50000000000000000000)
  directionLo := (282315424945970108373/50000000000000000000)
  directionHi := (564630849891940216747/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree129.table
  base := (130085691652196002958281420269786277011133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (13818846085)
      previous := (0)
      next := (12235864875)
      square := (314075487078060606883549433266912000000000000000)
      linear := (-44420092915115065164984811756448309600000000000000)
      constant := (1598413094890001524586267384140450374196735330583632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree129.table
  base := (813035571914477782313073036544099191891/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30246000000000000000000000000000000000000000
      center := (184529)
      previous := (0)
      next := (163300)
      square := (4192890980928185389153828318800000000000000)
      linear := (-593155594602603597702006333879540000000000000)
      constant := (21349318781552001542865840550360865186526962976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell148.Kernel129
