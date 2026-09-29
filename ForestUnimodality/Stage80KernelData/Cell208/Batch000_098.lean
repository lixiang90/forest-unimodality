import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell208.Parameters
import ForestUnimodality.BinomialMassData.Q21_37.Batch000_049
import ForestUnimodality.BinomialMassData.Q21_37.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_93.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_93.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree000.table
  base := (36426562479722554990217987/2000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (903)
      previous := (0)
      next := (688)
      square := (33013129185110648561307655800000000000000)
      linear := (-108076512066218420882179883800000000000000)
      constant := (6738914058748672673190327595000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree000.table
  base := (36426562479722554990217987/2000000000000000000000000)
  polynomial :=
    { denominator := 930000000000000000000000000000000000000000
      center := (2279)
      previous := (0)
      next := (1720)
      square := (82978946330142981518962486200000000000000)
      linear := (-271651773571846301136289978200000000000000)
      constant := (16938351553070988070451363955000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree001.table
  base := (22668211617246735325030207365958791826109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-5385382372224728812215577244200000000000000)
      constant := (157826996083461619760399078769187930049716105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree001.table
  base := (113066186177411822085820722993118574068063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-11353127751058954015561663836600000000000000)
      constant := (331604436441868971436817341257560849038225629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12377273584108965829/25000000000000000000)
  directionHi := (49509094336435863317/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree002.table
  base := (71272266038416580895120572406253540544509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-6771933797999376051790498787800000000000000)
      constant := (103684868953441991410637745901361097005432821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree002.table
  base := (70941381289587204006770085346016173498357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-14285050521390672695898338349000000000000000)
      constant := (217464126361237426631620697629764628195763231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/25000000000000000000)
  centralHi := (49509094336435863317/100000000000000000000)
  directionLo := (17504108167849146653/25000000000000000000)
  directionHi := (70016432671396586613/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree003.table
  base := (45337580266528441670447885906353237891133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-8158485223774023291365420331400000000000000)
      constant := (72417294935203363760794274589797582672961077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree003.table
  base := (11259711563927883032125746674094064556971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-17216973291722391376235012861400000000000000)
      constant := (151763500988116834476593144772052752470989572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17504108167849146653/25000000000000000000)
  centralHi := (70016432671396586613/100000000000000000000)
  directionLo := (85752266827427466151/100000000000000000000)
  directionHi := (10719033353428433269/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree004.table
  base := (7288116912549558636688335114582769945131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-9545036649548670530940341875000000000000000)
      constant := (55283848186957804401272941957055248219537356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree004.table
  base := (28912727743700830781297631404891222029177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-20148896062054110056571687373800000000000000)
      constant := (115919165166109093115926745856301393110117291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85752266827427466151/100000000000000000000)
  centralHi := (10719033353428433269/12500000000000000000)
  directionLo := (12377273584108965829/12500000000000000000)
  directionHi := (99018188672871726633/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree005.table
  base := (18868171016756512877548954464718301423697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-10931588075323317770515263418600000000000000)
      constant := (47015580139320840873031701196199354649041193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree005.table
  base := (18687799675626169678023123301400203417649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-23080818832385828736908361886200000000000000)
      constant := (98758842112545096531823127223936786453082067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/12500000000000000000)
  centralHi := (99018188672871726633/100000000000000000000)
  directionLo := (110705700440720433503/100000000000000000000)
  directionHi := (3459553138772513547/3125000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree006.table
  base := (2433189793699709643025728351517207539831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-12318139501097965010090184962200000000000000)
      constant := (44438133818834699931160920343335285610143195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree006.table
  base := (1203567242273056245832196503281134950283/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-26012741602717547417245036398600000000000000)
      constant := (93569784527718453047371624005995120616658890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110705700440720433503/100000000000000000000)
  centralHi := (3459553138772513547/3125000000000000000)
  directionLo := (121272018751584382379/100000000000000000000)
  directionHi := (6063600937579219119/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree007.table
  base := (7648232728903697500599763423897377542107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-13704690926872612249665106505800000000000000)
      constant := (45638237570442621228036576726515509855144483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree007.table
  base := (7556751762566208782316793073387562948843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-28944664373049266097581710911000000000000000)
      constant := (96316962268312154282705797157776343981514369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121272018751584382379/100000000000000000000)
  centralHi := (6063600937579219119/5000000000000000000)
  directionLo := (65494375625122841037/50000000000000000000)
  directionHi := (5239550050009827283/4000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree008.table
  base := (4472691765771796038003658181188655607891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-15091242352647259489240028049400000000000000)
      constant := (49462740895562579294891263050047269527202779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree008.table
  base := (4409764237406452311177380709209762570017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-31876587143380984777918385423400000000000000)
      constant := (104574983955700250012978103063051745489359011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65494375625122841037/50000000000000000000)
  centralHi := (5239550050009827283/4000000000000000000)
  directionLo := (17504108167849146653/12500000000000000000)
  directionHi := (5601314613711726929/4000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree009.table
  base := (2131648623835873102497702693294343338323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-16477793778421906728814949593000000000000000)
      constant := (55216633357934091209415427966719956030164187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree009.table
  base := (2089038632615994150533214406576542941939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-34808509913712703458255059935800000000000000)
      constant := (116885999478089173525718351204160173301610137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17504108167849146653/12500000000000000000)
  centralHi := (5601314613711726929/4000000000000000000)
  directionLo := (37131820752326897487/25000000000000000000)
  directionHi := (148527283009307589949/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree010.table
  base := (159562334860774931099881692650847015453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-17864345204196553968389871136600000000000000)
      constant := (62481030208467632350762430612478019128310314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree010.table
  base := (290628437057616103037464439356403677033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-37740432684044422138591734448200000000000000)
      constant := (132373731043870324757975631480664511800886139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37131820752326897487/25000000000000000000)
  centralHi := (148527283009307589949/100000000000000000000)
  directionLo := (156561502995279962819/100000000000000000000)
  directionHi := (7828075149763998141/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree011.table
  base := (-1149293664080091898776107270617043236213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-19250896629971201207964792680200000000000000)
      constant := (71003469273243493681384408821725267809624403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree011.table
  base := (-584080246481426639892514915506250950233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-40672355454376140818928408960600000000000000)
      constant := (150511471436773407423796055771590957020956522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156561502995279962819/100000000000000000000)
  centralHi := (7828075149763998141/5000000000000000000)
  directionLo := (6568123584970692367/4000000000000000000)
  directionHi := (20525386203033413647/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree012.table
  base := (-2384752281122604134178010268317478739761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-20637448055745848447539714223800000000000000)
      constant := (80631791810296862576600212333873371605267191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree012.table
  base := (-2397140432778022409753776624790320437709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-43604278224707859499265083473000000000000000)
      constant := (170982631867014511471903981877929506178084953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6568123584970692367/4000000000000000000)
  centralHi := (20525386203033413647/12500000000000000000)
  directionLo := (85752266827427466151/50000000000000000000)
  directionHi := (171504533654854932303/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree013.table
  base := (-863559641079221183830038097800734872089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-22023999481520495687114635767400000000000000)
      constant := (91274292092422719823200692062443175840440636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree013.table
  base := (-1731158134077461508369992906683951286483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-46536200995039578179601757985400000000000000)
      constant := (193596920248927284425080711740460336882139022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85752266827427466151/50000000000000000000)
  centralHi := (171504533654854932303/100000000000000000000)
  directionLo := (89253789115901647809/50000000000000000000)
  directionHi := (178507578231803295619/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree014.table
  base := (-4398125567655624418630275825617481617339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-23410550907295142926689557311000000000000000)
      constant := (102875699408705071830396268954329667665862909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree014.table
  base := (-4403361477748279870392191238085764039211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-49468123765371296859938432497800000000000000)
      constant := (218239957943550154772429522294598742274954687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89253789115901647809/50000000000000000000)
  centralHi := (178507578231803295619/100000000000000000000)
  directionLo := (185246068536413153961/100000000000000000000)
  directionHi := (92623034268206576981/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree015.table
  base := (-5240745935272916042029281906706955472551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-24797102333069790166264478854600000000000000)
      constant := (115402702369324345475693229081718177958077681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree015.table
  base := (-262206125062285936245879734284169938921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-52400046535703015540275107010200000000000000)
      constant := (244842995665263697464571050789174761321815140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185246068536413153961/100000000000000000000)
  centralHi := (92623034268206576981/50000000000000000000)
  directionLo := (38349579570165608351/20000000000000000000)
  directionHi := (47936974462707010439/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree016.table
  base := (-5996764806685816029609225260653952681143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-26183653758844437405839400398200000000000000)
      constant := (128835224398281690514509549661364738779515233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree016.table
  base := (-749866578862766445962019123048019755113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-55331969306034734220611781522600000000000000)
      constant := (273364710532497058901888881688420472368073768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38349579570165608351/20000000000000000000)
  centralHi := (47936974462707010439/25000000000000000000)
  directionLo := (12377273584108965829/6250000000000000000)
  directionHi := (39607275469148690653/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree017.table
  base := (-6675020760079727835083586924934676801539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-27570205184619084645414321941800000000000000)
      constant := (143161165482041289618711475152964427458693109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree017.table
  base := (-6676407111612452502754493044186810399157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-58263892076366452900948456035000000000000000)
      constant := (303780264794218144062474249610809425619230369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/6250000000000000000)
  centralHi := (39607275469148690653/20000000000000000000)
  directionLo := (204131225377794164919/100000000000000000000)
  directionHi := (5103280634444854123/2500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree018.table
  base := (-728084073944373971326870493889779590273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-28956756610393731884989243485400000000000000)
      constant := (158373233034282080967455438780648917409162630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree018.table
  base := (-7281724261874870099235983588882052134273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-61195814846698171581285130547400000000000000)
      constant := (336074729358196675301486822525653043696890941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204131225377794164919/100000000000000000000)
  centralHi := (5103280634444854123/2500000000000000000)
  directionLo := (52512324503547439959/25000000000000000000)
  directionHi := (210049298014189759837/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree019.table
  base := (-781743525233153871838650652809577246161/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-30343308036168379124564165029000000000000000)
      constant := (174467031870163066983511622172636887500055910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree019.table
  base := (-7817996584032811515763763192695788149931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-64127737617029890261621805059800000000000000)
      constant := (370239130880176552120616091923458042763748927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52512324503547439959/25000000000000000000)
  centralHi := (210049298014189759837/100000000000000000000)
  directionLo := (107902569499372914449/50000000000000000000)
  directionHi := (215805138998745828899/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree020.table
  base := (-2071684812080150769185933011071555748379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-31729859461943026364139086572600000000000000)
      constant := (191439913043712679975066097787372160721876596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree020.table
  base := (-1035886861707615270384191513142407876137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-67059660387361608941958479572200000000000000)
      constant := (406268075798856071800711033984883504744776232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107902569499372914449/50000000000000000000)
  centralHi := (215805138998745828899/100000000000000000000)
  directionLo := (110705700440720433503/50000000000000000000)
  directionHi := (221411400881440867007/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree021.table
  base := (-8689918910930581262840686737646080608737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-33116410887717673603714008116200000000000000)
      constant := (209290280049692521180527947737362515646639047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree021.table
  base := (-4345071837748030254839223196151581541791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-69991583157693327622295154084600000000000000)
      constant := (444158322224738871377048219771389980830033094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110705700440720433503/50000000000000000000)
  centralHi := (221411400881440867007/100000000000000000000)
  directionLo := (113439586192713409439/50000000000000000000)
  directionHi := (226879172385426818879/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree022.table
  base := (-4513838548528286363776110509891234941313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-34502962313492320843288929659800000000000000)
      constant := (228017170677013199451649501809117798730685006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree022.table
  base := (-4513909412081213793710029309609775036501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-72923505928025046302631828597000000000000000)
      constant := (483907921553623379274828453237990037139535234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113439586192713409439/50000000000000000000)
  centralHi := (226879172385426818879/100000000000000000000)
  directionLo := (116109118165101836343/50000000000000000000)
  directionHi := (232218236330203672687/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree023.table
  base := (-4650218711210062297420964794930487611011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-35889513739266968082863851203400000000000000)
      constant := (247620004995751916775724598859480324921051882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree023.table
  base := (-9300526604998875695049430563904100553003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-75855428698356764982968503109400000000000000)
      constant := (525515702522537684316752423278664478105692351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116109118165101836343/50000000000000000000)
  centralHi := (232218236330203672687/100000000000000000000)
  directionLo := (59359318827335585511/25000000000000000000)
  directionHi := (47487455061868468409/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree024.table
  base := (-9508455207842719731393500154854587693277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-37276065165041615322438772747000000000000000)
      constant := (268098433471704063108263270417604069447903787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree024.table
  base := (-950851122043189651564635113374187414869/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-78787351468688483663305177621800000000000000)
      constant := (568980961095886210980501098473422176829326730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59359318827335585511/25000000000000000000)
  centralHi := (47487455061868468409/20000000000000000000)
  directionLo := (121272018751584382379/50000000000000000000)
  directionHi := (242544037503168764759/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree025.table
  base := (-965188434516470493826025351543949260539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-38662616590816262562013694290600000000000000)
      constant := (289452245426940203678623520307363334623221090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree025.table
  base := (-386076778549624458114501914352354237337/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-81719274239020202343641852134200000000000000)
      constant := (614303274068645252259346548353054068343935725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121272018751584382379/50000000000000000000)
  centralHi := (242544037503168764759/100000000000000000000)
  directionLo := (12377273584108965829/5000000000000000000)
  directionHi := (247545471682179316581/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree026.table
  base := (-9730817596378829792562538090690130262831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-40049168016590909801588615834200000000000000)
      constant := (311681313870292264315727591543045211670184361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree026.table
  base := (-9730839579683633588214833116657306113067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-84651197009351921023978526646600000000000000)
      constant := (661482387031175726639275802833076986476027839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/5000000000000000000)
  centralHi := (247545471682179316581/100000000000000000000)
  directionLo := (31555979765224061749/12500000000000000000)
  directionHi := (252447838121792493993/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree027.table
  base := (-9745310881271955116561730332157019373887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-41435719442365557041163537377800000000000000)
      constant := (334785562247572032553899659762477040477148697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree027.table
  base := (-389812984875777832659483504445214672811/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-87583119779683639704315201159000000000000000)
      constant := (710518147029852302934626933844311152457147175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31555979765224061749/12500000000000000000)
  centralHi := (252447838121792493993/100000000000000000000)
  directionLo := (128628400241141199227/50000000000000000000)
  directionHi := (51451360096456479691/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree028.table
  base := (-9695397915154233262129331656601242026947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-42822270868140204280738458921400000000000000)
      constant := (358764944402519909823427639526112899665109557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree028.table
  base := (-77563251935423256878050714887087175141/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-90515042550015358384651875671400000000000000)
      constant := (761410462092492322728901869608965959258562125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128628400241141199227/50000000000000000000)
  centralHi := (51451360096456479691/20000000000000000000)
  directionLo := (65494375625122841037/25000000000000000000)
  directionHi := (261977502500491364149/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree029.table
  base := (-119763737884152441730153018388325711317/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-44208822293914851520313380465000000000000000)
      constant := (383619432499660655035889425545710568096562160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree029.table
  base := (-9581104377452373652807661026264572353883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-93446965320347077064988550183800000000000000)
      constant := (814159276901047915141365245647279237903755311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65494375625122841037/25000000000000000000)
  centralHi := (261977502500491364149/100000000000000000000)
  directionLo := (266614632453676601713/100000000000000000000)
  directionHi := (133307316226838300857/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree030.table
  base := (-1880485298972977276788881674213661045179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-45595373719689498759888302008600000000000000)
      constant := (409349009745664235533532042194007490145749745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree030.table
  base := (-4701214912011862547632231486843825451507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-96378888090678795745325224696200000000000000)
      constant := (868764558169681479142152769872858502446610638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266614632453676601713/100000000000000000000)
  centralHi := (133307316226838300857/50000000000000000000)
  directionLo := (135586238848585930443/50000000000000000000)
  directionHi := (271172477697171860887/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree031.table
  base := (-2289846928213374792835468011571041898073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-46981925145464145999463223552200000000000000)
      constant := (435953666002673318410644131135836974566152252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree031.table
  base := (-4579694891733458250107732306206024548993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 930000000000000000000000000000000000000000
      center := (2279)
      previous := (0)
      next := (1720)
      square := (82978946330142981518962486200000000000000)
      linear := (-3203574543903564981472964490600000000000000)
      constant := (29846009221170376428528376265445679433887302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135586238848585930443/50000000000000000000)
  centralHi := (271172477697171860887/100000000000000000000)
  directionLo := (275654971082397271513/100000000000000000000)
  directionHi := (137827485541198635757/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree032.table
  base := (-553249197474567616737362609972821226781/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-48368476571238793239038145095800000000000000)
      constant := (463433395144556582726338243650355323848588976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree032.table
  base := (-8851988446098563904208715639666189623311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-102242733631342233105998573721000000000000000)
      constant := (983544447880165681534677901438042375315994387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275654971082397271513/100000000000000000000)
  centralHi := (137827485541198635757/50000000000000000000)
  directionLo := (280065730685586346449/100000000000000000000)
  directionHi := (5601314613711726929/2000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree033.table
  base := (-4240113771717398815537639695874462250623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-49755027997013440478613066639400000000000000)
      constant := (491788193463581286117636720642695722357794226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree033.table
  base := (-1060028542747659790035504561755470257511/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-105174656401673951786335248233400000000000000)
      constant := (1043719036947163008342453679176071833980766296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280065730685586346449/100000000000000000000)
  centralHi := (5601314613711726929/2000000000000000000)
  directionLo := (35551011748627116107/12500000000000000000)
  directionHi := (284408093989016928857/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree034.table
  base := (-251378453363235424621564064803166791107/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-51141579422788087718187988183000000000000000)
      constant := (521018058710145178108065707028702869215184544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree034.table
  base := (-8044111002834255345725493477830401611907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-108106579172005670466671922745800000000000000)
      constant := (1105750048641327208800737034293414952152872119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35551011748627116107/12500000000000000000)
  centralHi := (284408093989016928857/100000000000000000000)
  directionLo := (288685147433115431167/100000000000000000000)
  directionHi := (1127676357160607153/390625000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree035.table
  base := (-7543637053046033353202357189514781343193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-52528130848562734957762909726600000000000000)
      constant := (551122989514034306688744629615554264341168783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree035.table
  base := (-7543637359880606219392131478260998859369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-111038501942337389147008597258200000000000000)
      constant := (1169637480277942053207897340380173540288439173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288685147433115431167/100000000000000000000)
  centralHi := (1127676357160607153/390625000000000000)
  directionLo := (36612469010419988911/12500000000000000000)
  directionHi := (292899752083359911289/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree036.table
  base := (-1744701948255524406854705808032568000169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-53914682274337382197337831270200000000000000)
      constant := (582102985035613864700816822210413657631074556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree036.table
  base := (-6978807982982963162050138075071107372789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-113970424712669107827345271770600000000000000)
      constant := (1235381330214093572871465678643969997444249313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36612469010419988911/12500000000000000000)
  centralHi := (292899752083359911289/100000000000000000000)
  directionLo := (37131820752326897487/12500000000000000000)
  directionHi := (297054566018615179897/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree037.table
  base := (-3174811553437098465996508767228895584119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (903)
      previous := (0)
      next := (688)
      square := (33013129185110648561307655800000000000000)
      linear := (-1494627937840865660457101427400000000000000)
      constant := (16593460669070037567578712118825061726775194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree037.table
  base := (-1587405806097009253322552945610027268173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-116902347483000826507681946283000000000000000)
      constant := (1302981597434254500440902065268425165543428964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37131820752326897487/12500000000000000000)
  centralHi := (297054566018615179897/100000000000000000000)
  directionLo := (150576031969335934921/50000000000000000000)
  directionHi := (301152063938671869843/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree038.table
  base := (-113121664649894655068818719643145826927/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-56687785125886676676487674357400000000000000)
      constant := (646688168348292184952490809806426668146846850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree038.table
  base := (-5656083305138241104281935653830525892707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-119834270253332545188018620795400000000000000)
      constant := (1372438281301159558282444592310406593851325719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150576031969335934921/50000000000000000000)
  centralHi := (301152063938671869843/100000000000000000000)
  directionLo := (61038910880367456217/20000000000000000000)
  directionHi := (152597277200918640543/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree039.table
  base := (-97963766442992141359213354496627053649/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-58074336551661323916062595901000000000000000)
      constant := (680293355605264229751637022394305878177725950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree039.table
  base := (-1224547091756139972505347504173368111601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-122766193023664263868355295307800000000000000)
      constant := (1443751381406025338212339560185872718937017268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61038910880367456217/20000000000000000000)
  centralHi := (152597277200918640543/50000000000000000000)
  directionLo := (15459209751677971961/5000000000000000000)
  directionHi := (309184195033559439221/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree040.table
  base := (-81518769522514623339624401333708025523/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-59460887977435971155637517444600000000000000)
      constant := (714773606389214742839884675160707685652950650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree040.table
  base := (-203796925191433483292857267743359986763/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-125698115793995982548691969820200000000000000)
      constant := (1516920897478479267471097040189917863163245420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15459209751677971961/5000000000000000000)
  centralHi := (309184195033559439221/100000000000000000000)
  directionLo := (156561502995279962819/50000000000000000000)
  directionHi := (313123005990559925639/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree041.table
  base := (-797333440756450267053571709185794041221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-60847439403210618395212438988200000000000000)
      constant := (750128920606226633368986459253698591830273804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree041.table
  base := (-797333445029288243706261562523492598557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-128630038564327701229028644332600000000000000)
      constant := (1591946829332375888587144692393379083353440676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156561502995279962819/50000000000000000000)
  centralHi := (313123005990559925639/100000000000000000000)
  directionLo := (317012881918981855047/100000000000000000000)
  directionHi := (39626610239872731881/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree042.table
  base := (-55959355800390784677517439126849680893/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-62233990828985265634787360531800000000000000)
      constant := (786359298188991901130403879046613711474299320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree042.table
  base := (-2238374242553889400183907520172178270773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-131561961334659419909365318845000000000000000)
      constant := (1668829176833183236721947353676543610045361441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317012881918981855047/100000000000000000000)
  centralHi := (39626610239872731881/12500000000000000000)
  directionLo := (320855602607453994309/100000000000000000000)
  directionHi := (32085560260745399431/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree043.table
  base := (-1223059920221224670996696365022980119907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-63620542254759912874362282075400000000000000)
      constant := (823464739086685048636806236348283540215847317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree043.table
  base := (-122305992671526878479195876377538562497/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-134493884104991138589701993357400000000000000)
      constant := (1747567939878334579958544748106435563243211490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320855602607453994309/100000000000000000000)
  centralHi := (32085560260745399431/10000000000000000000)
  directionLo := (1298611370020186103/400000000000000000)
  directionHi := (324652842505046525751/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree044.table
  base := (-28678171440459498833047405092012667169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-65007093680534560113937203619000000000000000)
      constant := (861445243258838823898027547421745173293228195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree044.table
  base := (-17923857650249161370828955209006830251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-137425806875322857270038667869800000000000000)
      constant := (1828163118385374093962975720205059466467090936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1298611370020186103/400000000000000000)
  centralHi := (324652842505046525751/100000000000000000000)
  directionLo := (328406179248534618351/100000000000000000000)
  directionHi := (20525386203033413647/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree045.table
  base := (500316466168322730348788200106590657019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-66393645106309207353512125162600000000000000)
      constant := (900300810671632760003456845817891845218918022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree045.table
  base := (1000632929874495109469161250297306783977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-140357729645654575950375342382200000000000000)
      constant := (1910614712284788491530474812958607135458205691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328406179248534618351/100000000000000000000)
  centralHi := (20525386203033413647/6250000000000000000)
  directionLo := (332117101322161300509/100000000000000000000)
  directionHi := (33211710132216130051/10000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree046.table
  base := (2209011426897991596776408631872642316411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-67780196532083854593087046706200000000000000)
      constant := (940031441295636625308053937538233647331166659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree046.table
  base := (441802285076615558795001183087684320539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-143289652415986294630712016894600000000000000)
      constant := (1994922721515656757672258012814608969480569685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332117101322161300509/100000000000000000000)
  centralHi := (33211710132216130051/10000000000000000000)
  directionLo := (335787014955386357239/100000000000000000000)
  directionHi := (8394675373884658931/2500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree047.table
  base := (435218075897975306418585993137410873767/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-69166747957858501832661968249800000000000000)
      constant := (980637135104431542056351621892040923889496184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree047.table
  base := (1740872303126072514451855617626191398669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-146221575186318013311048691407000000000000000)
      constant := (2081087146022995441526220467778432619604725454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335787014955386357239/100000000000000000000)
  centralHi := (8394675373884658931/2500000000000000000)
  directionLo := (339417250349275805361/100000000000000000000)
  directionHi := (169708625174637902681/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree048.table
  base := (4818832455475597245906890073104880526819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-70553299383633149072236889793400000000000000)
      constant := (1022117892073760910062573098158080581441215211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree048.table
  base := (2409416227451447958016880383355340578389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-149153497956649731991385365919400000000000000)
      constant := (2169107985756124860102789545944826893774990974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339417250349275805361/100000000000000000000)
  centralHi := (169708625174637902681/50000000000000000000)
  directionLo := (68601813461941972921/20000000000000000000)
  directionHi := (171504533654854932303/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree049.table
  base := (6220274955248002959942874634067077277643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-71939850809407796311811811337000000000000000)
      constant := (1064473712181001493661642722153637828793093267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree049.table
  base := (777534369362013619938251599101736982033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-152085420726981450671722040431800000000000000)
      constant := (2258985240667650737829403341743682461753609112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68601813461941972921/20000000000000000000)
  centralHi := (171504533654854932303/50000000000000000000)
  directionLo := (86640915088762760803/25000000000000000000)
  directionHi := (346563660355051043213/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree050.table
  base := (960759011365496867462566247665475929903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-73326402235182443551386732880600000000000000)
      constant := (1107704595404828318722568377034432292384297656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree050.table
  base := (960759011338480628294096968409187388239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-155017343497313169352058714944200000000000000)
      constant := (2350718910712817558185716000389389497922344296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86640915088762760803/25000000000000000000)
  centralHi := (346563660355051043213/100000000000000000000)
  directionLo := (350082163356982933061/100000000000000000000)
  directionHi := (175041081678491466531/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree051.table
  base := (1843244769543190153878615903909669758389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-74712953660957090790961654424200000000000000)
      constant := (1151810541724997212298137965641461689496172705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree051.table
  base := (4608111923791629435416608239455631993503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-157949266267644888032395389456600000000000000)
      constant := (2444308995849087102328256699907101174074538298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350082163356982933061/100000000000000000000)
  centralHi := (175041081678491466531/50000000000000000000)
  directionLo := (70713130753126576449/20000000000000000000)
  directionHi := (176782826882816441123/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree052.table
  base := (675670638219961763754319854682325358809/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-76099505086731738030536575967800000000000000)
      constant := (1196791551122199056076917013744161654659352336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree052.table
  base := (10810730211437953952085172690497897452667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-160881189037976606712732063969000000000000000)
      constant := (2539755496035854055029719826393905438356038961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70713130753126576449/20000000000000000000)
  centralHi := (176782826882816441123/50000000000000000000)
  directionLo := (357015156463606591237/100000000000000000000)
  directionHi := (178507578231803295619/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree053.table
  base := (12469591168838446513877790352188850302763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-77486056512506385270111497511400000000000000)
      constant := (1242647623577958044034027702086146536064482547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree053.table
  base := (12469591168788487988781792548092748010869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-163813111808308325393068738481400000000000000)
      constant := (2637058411234245652193040066012551392515335327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357015156463606591237/100000000000000000000)
  centralHi := (178507578231803295619/50000000000000000000)
  directionLo := (22526977955500551693/6250000000000000000)
  directionHi := (360431647288008827089/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree054.table
  base := (7096403353365794278527952689645971730753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-78872607938281032509686419055000000000000000)
      constant := (1289378759074557211888108220583850670598801714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree054.table
  base := (4435252095844047109998680852699458703/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-166745034578640044073405412993800000000000000)
      constant := (2736217741406973430628220020580664126210396800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22526977955500551693/6250000000000000000)
  centralHi := (360431647288008827089/100000000000000000000)
  directionLo := (181908028127376573569/50000000000000000000)
  directionHi := (363816056254753147139/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree055.table
  base := (3995094203192428254003773816263577983979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-80259159364055679749261340598600000000000000)
      constant := (1336984957594981119913476094141859353040269004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree055.table
  base := (7990188406375465180269805896159010532673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-169676957348971762753742087506200000000000000)
      constant := (2837233486518217810881796071553252854731392518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181908028127376573569/50000000000000000000)
  centralHi := (363816056254753147139/100000000000000000000)
  directionLo := (367169270515352104449/100000000000000000000)
  directionHi := (7343385410307042089/2000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree056.table
  base := (8916150737501168102843892911682685817931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-81645710789830326988836262142200000000000000)
      constant := (1385466219122869555945273813699387193769495078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree056.table
  base := (17832301474990825206891870228520003534571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-172608880119303481434078762018600000000000000)
      constant := (2940105646533533857519283960715223170190168193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367169270515352104449/100000000000000000000)
  centralHi := (7343385410307042089/2000000000000000000)
  directionLo := (185246068536413153961/50000000000000000000)
  directionHi := (370492137072826307923/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree057.table
  base := (9874290340964549085243646820401348153699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-83032262215604974228411183685800000000000000)
      constant := (1434822543642478527204303209663458891244827862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree057.table
  base := (19748580681922045870465100050462793477221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-175540802889635200114415436531000000000000000)
      constant := (3044834221419771137241130058222684233594828143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185246068536413153961/50000000000000000000)
  centralHi := (370492137072826307923/100000000000000000000)
  directionLo := (186892732640145764167/50000000000000000000)
  directionHi := (74757093056058305667/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree058.table
  base := (10864607211237462514901379816250037798653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-84418813641379621467986105229400000000000000)
      constant := (1485053931138646257548008015946892603492711914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree058.table
  base := (5432303605617651428085468621664719931793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-178472725659966918794752111043400000000000000)
      constant := (3151419211145003346567335422693437550253436876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186892732640145764167/50000000000000000000)
  centralHi := (74757093056058305667/20000000000000000000)
  directionLo := (94262507285776846553/25000000000000000000)
  directionHi := (377050029143107386213/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree059.table
  base := (11887101342983908865285336456622242277157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-85805365067154268707561026773000000000000000)
      constant := (1536160381596762780272744286147831699354855866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree059.table
  base := (23774202685965173065895342315396943472577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-181404648430298637475088785555800000000000000)
      constant := (3259860615678465036303014842055289388031439491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94262507285776846553/25000000000000000000)
  centralHi := (377050029143107386213/100000000000000000000)
  directionLo := (380286569443140122763/100000000000000000000)
  directionHi := (95071642360785030691/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree060.table
  base := (25883545462118622715590286444375826639123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-87191916492928915947135948316600000000000000)
      constant := (1588141895002742244158704197570350506668959387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree060.table
  base := (25883545462117003884305503298152977138123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-184336571200630356155425460068200000000000000)
      constant := (3370158434990493757361186255620575033089208609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380286569443140122763/100000000000000000000)
  centralHi := (95071642360785030691/25000000000000000000)
  directionLo := (38349579570165608351/10000000000000000000)
  directionHi := (383495795701656083511/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree061.table
  base := (1122289709640094928413872832208906038309/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-88578467918703563186710869860200000000000000)
      constant := (1640998471342997369691577017187549809161125525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree061.table
  base := (5611448548200276515751229788192133916231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-187268493970962074835762134580600000000000000)
      constant := (3482312669052476554699292534301189610402469865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38349579570165608351/10000000000000000000)
  centralHi := (383495795701656083511/100000000000000000000)
  directionLo := (386678387995580180051/100000000000000000000)
  directionHi := (96669596998895045013/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree062.table
  base := (7573823628260232848300509353438564714853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-89965019344478210426285791403800000000000000)
      constant := (1694730110604415686193539996380629580378535028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree062.table
  base := (29585248547890942720919382614738131113/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 930000000000000000000000000000000000000000
      center := (2279)
      previous := (0)
      next := (1720)
      square := (82978946330142981518962486200000000000000)
      linear := (-6135497314235283661809639003000000000000000)
      constant := (116010429607638712935910006646366741702153216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386678387995580180051/100000000000000000000)
  centralHi := (96669596998895045013/25000000000000000000)
  directionLo := (194917499320144772867/50000000000000000000)
  directionHi := (77966999728057909147/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree063.table
  base := (4074712596123343511681446482270638181227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-91351570770252857665860712947400000000000000)
      constant := (1749336812774337298849898860269828029360798104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree063.table
  base := (2037356298061648588952808854281041494241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-193132339511625512196435483605400000000000000)
      constant := (3712190381316803984219894301840675882046348848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194917499320144772867/50000000000000000000)
  centralHi := (77966999728057909147/20000000000000000000)
  directionLo := (196483126875368523111/50000000000000000000)
  directionHi := (392966253750737046223/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree064.table
  base := (34964461499907609798988942275812711937069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-92738122196027504905435634491000000000000000)
      constant := (1804818577840534007362579835185187602641847461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree064.table
  base := (6992892299981476629362141261108466079323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-196064262281957230876772158117800000000000000)
      constant := (3829913859466736799542869912102878538533441045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196483126875368523111/50000000000000000000)
  centralHi := (392966253750737046223/100000000000000000000)
  directionLo := (12377273584108965829/3125000000000000000)
  directionHi := (396072754691486906529/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree065.table
  base := (37395576697172275852826486266006583116849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-94124673621802152145010556034600000000000000)
      constant := (1861175405791189643272166811300163012286966281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree065.table
  base := (18697788348586068648253811275909570947569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-198996185052288949557108832630200000000000000)
      constant := (3949493752261714782331691780294894586083682854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377273584108965829/3125000000000000000)
  centralHi := (396072754691486906529/100000000000000000000)
  directionLo := (399155079425173880627/100000000000000000000)
  directionHi := (99788769856293470157/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree066.table
  base := (39891046352436929717852104013449614001361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-95511225047576799384585477578200000000000000)
      constant := (1918407296614881521739353323967612521567863209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree066.table
  base := (19945523176218422518010885824881263043737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-201928107822620668237445507142600000000000000)
      constant := (4070930059677682772073266878638665362710187542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399155079425173880627/100000000000000000000)
  centralHi := (99788769856293470157/25000000000000000000)
  directionLo := (201106891883974835771/50000000000000000000)
  directionHi := (402213783767949671543/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree067.table
  base := (42450870457632381868256091600182187102203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-96897776473351446624160399121800000000000000)
      constant := (1976514250300562922303305888523849414142915907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree067.table
  base := (5306358807204041265611087417159143013133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-204860030592952386917782181655000000000000000)
      constant := (4194222781691377333666336185496558474454899512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201106891883974835771/50000000000000000000)
  centralHi := (402213783767949671543/100000000000000000000)
  directionLo := (405249402559639907923/100000000000000000000)
  directionHi := (101312350639909976981/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree068.table
  base := (11268762251237992773871314691417723033667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-98284327899126093863735320665400000000000000)
      constant := (2035496266837546525769515187502203451332360492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree068.table
  base := (45075049004951939485619761870343828861801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-207791953363284105598118856167400000000000000)
      constant := (4319371918280291886288499940954601258608572283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405249402559639907923/100000000000000000000)
  centralHi := (101312350639909976981/25000000000000000000)
  directionLo := (204131225377794164919/50000000000000000000)
  directionHi := (408262450755588329839/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree069.table
  base := (47763581986840117522279694321561487983687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-99670879324900741103310242209000000000000000)
      constant := (2095353346215488743286012402485817677049667503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree069.table
  base := (47763581986840098216073541730265575237413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-210723876133615824278455530679800000000000000)
      constant := (4446377469422643707496884438306355653409461679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204131225377794164919/50000000000000000000)
  centralHi := (408262450755588329839/100000000000000000000)
  directionLo := (411253424446500252737/100000000000000000000)
  directionHi := (205626712223250126369/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree070.table
  base := (25258234697990742718854269709294239403813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-101057430750675388342885163752600000000000000)
      constant := (2156085488424374880264533187710047627487639994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree070.table
  base := (25258234697990736824309501793156768826429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-213655798903947542958792205192200000000000000)
      constant := (4575239435097342693210709402693341929053189614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411253424446500252737/100000000000000000000)
  centralHi := (205626712223250126369/50000000000000000000)
  directionLo := (414222801812004788369/100000000000000000000)
  directionHi := (41422280181200478837/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree071.table
  base := (2133348449011628712920388340667584449699/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-102443982176450035582460085296200000000000000)
      constant := (2217692693454505082946392248070548077790948275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree071.table
  base := (26666855612645355312808360261146677853269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-216587721674279261639128879704600000000000000)
      constant := (4705957815283961764510500366316171744501949054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414222801812004788369/100000000000000000000)
  centralHi := (41422280181200478837/10000000000000000000)
  directionLo := (41717104401312599139/10000000000000000000)
  directionHi := (417171044013125991391/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree072.table
  base := (5621530746790270750814281181770227670171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-103830533602224682822035006839800000000000000)
      constant := (2280174961296481019615804289933634416804640990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree072.table
  base := (56215307467902703114909480754653977868331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-219519644444610980319465554217000000000000000)
      constant := (4838532609962708820705548087602867418194398273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41717104401312599139/10000000000000000000)
  centralHi := (417171044013125991391/100000000000000000000)
  directionLo := (420098596028379519673/100000000000000000000)
  directionHi := (210049298014189759837/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree073.table
  base := (29580629058581686254600045382343073113363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-105217085027999330061609928383400000000000000)
      constant := (2343532291941193252036799591834855334184387894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree073.table
  base := (59161258117163369828119902771316741064219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-222451567214942698999802228729400000000000000)
      constant := (4972963819114400145441460575654106164488143377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420098596028379519673/100000000000000000000)
  centralHi := (210049298014189759837/50000000000000000000)
  directionLo := (423005887437786986669/100000000000000000000)
  directionHi := (42300588743778698667/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree074.table
  base := (621715631666209053849881434015718300021/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (903)
      previous := (0)
      next := (688)
      square := (33013129185110648561307655800000000000000)
      linear := (-2881179363615512900032022971000000000000000)
      constant := (65074721226481331238442821256658157710077700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree074.table
  base := (62171563166620903749098145958133692196981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-225383489985274417680138903241800000000000000)
      constant := (5109251442720435179090677839979299434603896223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423005887437786986669/100000000000000000000)
  centralHi := (42300588743778698667/10000000000000000000)
  directionLo := (425893333158719238591/100000000000000000000)
  directionHi := (6654583330604988103/1562500000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree075.table
  base := (32623111305008734250852155947493034363999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-107990187879548624540759771470600000000000000)
      constant := (2472872141603762051251882835344235928088629262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree075.table
  base := (65246222610017467503730055148890470058153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-228315412755606136360475577754200000000000000)
      constant := (5247395480762772576503628771234251225177655099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425893333158719238591/100000000000000000000)
  centralHi := (6654583330604988103/1562500000000000000)
  directionLo := (107190333534284332689/25000000000000000000)
  directionHi := (428761334137137330757/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree076.table
  base := (3419261822064065448016837289527603953103/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-109376739305323271780334693014200000000000000)
      constant := (2538854660604739408606547715106465796235960140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree076.table
  base := (34192618220640654175815340029741237240053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-231247335525937855040812252266600000000000000)
      constant := (5387395933223907474529783557749887973926145598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107190333534284332689/25000000000000000000)
  centralHi := (428761334137137330757/100000000000000000000)
  directionLo := (107902569499372914449/25000000000000000000)
  directionHi := (431610277997491657797/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree077.table
  base := (35794302327259634327923275425741033028701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-110763290731097919019909614557800000000000000)
      constant := (2605712242374673594440580779572878948432583338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree077.table
  base := (17897151163629817071158855364769955219269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-234179258296269573721148926779000000000000000)
      constant := (5529252800086849898631603659943727123588610108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107902569499372914449/25000000000000000000)
  centralHi := (431610277997491657797/100000000000000000000)
  directionLo := (434440539654261705187/100000000000000000000)
  directionHi := (108610134913565426297/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree078.table
  base := (2994253089760386660904265865823231240227/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-112149842156872566259484536101400000000000000)
      constant := (2673444886905731627375138555631800089196769075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree078.table
  base := (74856327244009666296266623451500820819037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-237111181066601292401485601291400000000000000)
      constant := (5672966081335104242467413995867076866421283671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434440539654261705187/100000000000000000000)
  centralHi := (108610134913565426297/25000000000000000000)
  directionLo := (437252481887867896413/100000000000000000000)
  directionHi := (218626240943933948207/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree079.table
  base := (39094202102097765746214144558323789727419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-113536393582647213499059457645000000000000000)
      constant := (2742052594190306014017870652670290536273673222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree079.table
  base := (19547101051048882838610923884230832359303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-240043103836933011081822275803800000000000000)
      constant := (5818535776952649758551726223108949958767482196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437252481887867896413/100000000000000000000)
  centralHi := (218626240943933948207/50000000000000000000)
  directionLo := (220023227943730039077/50000000000000000000)
  directionHi := (88009291177492015631/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree080.table
  base := (81584835529678166061150197559113271473847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-114922945008421860738634379188600000000000000)
      constant := (2811535364221005937485580277402426068647696543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree080.table
  base := (4079241776483908298852175660970927560133/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-242975026607264729762158950316200000000000000)
      constant := (5965961886923922002043579373747583683117268780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220023227943730039077/50000000000000000000)
  centralHi := (88009291177492015631/20000000000000000000)
  directionLo := (110705700440720433503/25000000000000000000)
  directionHi := (442822801762881734013/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree081.table
  base := (21261405303802755409010406520243057695727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-116309496434196507978209300732200000000000000)
      constant := (2881893196990648872754819038702050983941801052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree081.table
  base := (85045621215211021584783488024242613821897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-245906949377596448442495624828600000000000000)
      constant := (6115244411233795173388901745210291455648529051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110705700440720433503/25000000000000000000)
  centralHi := (442822801762881734013/100000000000000000000)
  directionLo := (111395462256980692461/25000000000000000000)
  directionHi := (89116369805584553969/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree082.table
  base := (88570761255693868026458452539222049390633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-117696047859971155217784222275800000000000000)
      constant := (2953126092492252604694595133355394985615776577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree082.table
  base := (88570761255693867995224337467657919217007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-248838872147928167122832299341000000000000000)
      constant := (6266383349867565308971720886096457781102631181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111395462256980692461/25000000000000000000)
  centralHi := (89116369805584553969/20000000000000000000)
  directionLo := (44832391705680466129/10000000000000000000)
  directionHi := (448323917056804661291/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree083.table
  base := (46080127823083620275278990627158138192257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-119082599285745802457359143819400000000000000)
      constant := (3025234050719027626155465910977158982370399666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree083.table
  base := (18432051129233448106305662261205859090323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-251770794918259885803168973853400000000000000)
      constant := (6419378702810934272128713562453682458787006045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44832391705680466129/10000000000000000000)
  centralHi := (448323917056804661291/100000000000000000000)
  directionLo := (112762328878922029823/25000000000000000000)
  directionHi := (451049315515688119293/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree084.table
  base := (3832564175272285970680091281263720173661/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-120469150711520449696934065363000000000000000)
      constant := (3098217071664369894907739745130850822943547725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree084.table
  base := (23953526095451787313852489424271788235213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-254702717688591604483505648365800000000000000)
      constant := (6574230470049994499867802816620702261928476316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112762328878922029823/25000000000000000000)
  centralHi := (451049315515688119293/100000000000000000000)
  directionLo := (453758344770853637757/100000000000000000000)
  directionHi := (226879172385426818879/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree085.table
  base := (24883076864480008951883862258886772050833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-121855702137295096936508986906600000000000000)
      constant := (3172075155321853929545274300727663963750361508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree085.table
  base := (12441538432240004475059342122216052552213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-257634640458923323163842322878200000000000000)
      constant := (6730938651571214463418673190748791036064240632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453758344770853637757/100000000000000000000)
  centralHi := (226879172385426818879/50000000000000000000)
  directionLo := (57056412034384742779/12500000000000000000)
  directionHi := (456451296275077942233/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree086.table
  base := (103314864869937964188792151593988903559343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-123242253563069744176083908450200000000000000)
      constant := (3246808301685226225706842440077370808972740567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree086.table
  base := (103314864869937964184492169687499067313749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-260566563229255041844178997390600000000000000)
      constant := (6889503247361424803344554212553459811065538367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57056412034384742779/12500000000000000000)
  centralHi := (456451296275077942233/100000000000000000000)
  directionLo := (229564226466806609137/50000000000000000000)
  directionHi := (18365138117344528731/4000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree087.table
  base := (21432355322682806564807491463539047999661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-124628804988844391415658829993800000000000000)
      constant := (3322416510748398975120204040739124783557679545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree087.table
  base := (107161776613414032821419115782342963626619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-263498485999586760524515671903000000000000000)
      constant := (7049924257407805102372883509287694764135542577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229564226466806609137/50000000000000000000)
  centralHi := (18365138117344528731/4000000000000000000)
  directionLo := (5772376118138374483/1250000000000000000)
  directionHi := (461790089451069958641/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree088.table
  base := (111073042684017995741818479789266535633629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-126015356414619038655233751537400000000000000)
      constant := (3398899782505444071050440101207505887282438101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree088.table
  base := (111073042684017995740224331035252247921299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-266430408769918479204852346415400000000000000)
      constant := (7212201681697871261369178003845032230757105017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5772376118138374483/1250000000000000000)
  centralHi := (461790089451069958641/100000000000000000000)
  directionLo := (464436472660407345373/100000000000000000000)
  directionHi := (232218236330203672687/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree089.table
  base := (57524331538766040876266884161700560304491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-127401907840393685894808673081000000000000000)
      constant := (3476258116950587384738986235494336134113696358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree089.table
  base := (115048663077532081751563312943815565419979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-269362331540250197885189020927800000000000000)
      constant := (7376335520219463445994557495511020275105799457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464436472660407345373/100000000000000000000)
  centralHi := (232218236330203672687/50000000000000000000)
  directionLo := (93413572367029279617/20000000000000000000)
  directionHi := (233533930917573199043/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree090.table
  base := (29772159447461750247314473833779541227113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-128788459266168333134383594624600000000000000)
      constant := (3554491514078203298358021533235776767759670788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree090.table
  base := (29772159447461750247166798575059133201079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-272294254310581916565525695440200000000000000)
      constant := (7542325772960734573563127340125581924074843028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93413572367029279617/20000000000000000000)
  centralHi := (233533930917573199043/50000000000000000000)
  directionLo := (469684508985839888457/100000000000000000000)
  directionHi := (234842254492919944229/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree091.table
  base := (123192966816958128889127482433661374613381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-130175010691942980373958516168200000000000000)
      constant := (3633599973882809480880986029414882421845718589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree091.table
  base := (123192966816958128888767976108710275813673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-275226177080913635245862369952600000000000000)
      constant := (7710172439910139311460427396583811725170819259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469684508985839888457/100000000000000000000)
  centralHi := (234842254492919944229/50000000000000000000)
  directionLo := (118071664785439635291/25000000000000000000)
  directionHi := (94457331828351708233/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree092.table
  base := (63680825077480929139658833672376106566871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-131561562117717627613533437711800000000000000)
      constant := (3713583496359061894088282487578165779780092798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree092.table
  base := (127361650154961858279098894630378471397009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-278158099851245353926199044465000000000000000)
      constant := (7879875521056423560207371085026581133037576947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118071664785439635291/25000000000000000000)
  centralHi := (94457331828351708233/20000000000000000000)
  directionLo := (59359318827335585511/12500000000000000000)
  directionHi := (474874550618684684089/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree093.table
  base := (16449335975006513848753009069196869993533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-132948113543492274853108359255400000000000000)
      constant := (3794442081501750016691648714907844120169173416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree093.table
  base := (65797343900026055394945478511895788345079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 930000000000000000000000000000000000000000
      center := (2279)
      previous := (0)
      next := (1720)
      square := (82978946330142981518962486200000000000000)
      linear := (-9067420084567002342146313515400000000000000)
      constant := (259723710206084335350448851583612616632184694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59359318827335585511/12500000000000000000)
  centralHi := (474874550618684684089/100000000000000000000)
  directionLo := (95489683054728342303/20000000000000000000)
  directionHi := (119362103818410427879/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree094.table
  base := (67946039874258499669313922051254845617553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-134334664969266922092683280799000000000000000)
      constant := (3876175729305792275274979500335935767300860114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree094.table
  base := (135892079748516999338546857283296713933459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-284021945391908791286872393489800000000000000)
      constant := (8224850925896010447970929305565744426270162297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95489683054728342303/20000000000000000000)
  centralHi := (119362103818410427879/25000000000000000000)
  directionLo := (120002119686832494101/25000000000000000000)
  directionHi := (96001695749465995281/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree095.table
  base := (140253825996735633916893045441429314232779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-135721216395041569332258202342600000000000000)
      constant := (3958784439766231671416999846725316731184674451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree095.table
  base := (140253825996735633916843779014058804930011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-286953868162240509967209068002200000000000000)
      constant := (8400123249568172690634709424781531534613221713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120002119686832494101/25000000000000000000)
  centralHi := (96001695749465995281/20000000000000000000)
  directionLo := (96510992138997315213/20000000000000000000)
  directionHi := (241277480347493288033/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree096.table
  base := (36169981635293765842245640554899965833797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-137107767820816216571833123886200000000000000)
      constant := (4042268212878231594985368744529832212905872372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree096.table
  base := (144679926541175063368952595449408697244223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-289885790932572228647545742514600000000000000)
      constant := (8577251987394915625672999384271045274155094909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96510992138997315213/20000000000000000000)
  centralHi := (241277480347493288033/50000000000000000000)
  directionLo := (485088075006337529517/100000000000000000000)
  directionHi := (242544037503168764759/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree097.table
  base := (74585190689193673137237519490570849241747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-138494319246590863811408045429800000000000000)
      constant := (4126627048637071814175529358130382985223903286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree097.table
  base := (29834076275677469254891362675326358156423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-292817713702903947327882417027000000000000000)
      constant := (8756237139366298837970738434102029452824837545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell208.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485088075006337529517/100000000000000000000)
  centralHi := (242544037503168764759/50000000000000000000)
  directionLo := (243804015007632847363/50000000000000000000)
  directionHi := (487608030015265694727/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree098.table
  base := (153725190505006744449462218211491394717517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (33411)
      previous := (0)
      next := (25456)
      square := (1221485779849093996768383264600000000000000)
      linear := (-139880870672365511050982966973400000000000000)
      constant := (4211860947038144633413711282989531719368280773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree098.table
  base := (768625952525033722247255673413917685929/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (70649)
      previous := (0)
      next := (53320)
      square := (2572347336234432427087837072200000000000000)
      linear := (-295749636473235666008219091539400000000000000)
      constant := (8937078705472618904343727599814864937706661400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell208.Kernel098
