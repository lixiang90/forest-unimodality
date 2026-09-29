import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell169.Parameters
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch000_049
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch050_099
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch000_049
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree000.table
  base := (110978221579827266265994013/2500000000000000000000000)
  polynomial :=
    { denominator := 455820000000000000000000000000000000000000000
      center := (2352929)
      previous := (0)
      next := (2068525)
      square := (90326847583926171718071706447200000000000000)
      linear := (-360490526409326748868977575850000000000000000)
      constant := (20234437184206745803746156402264000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree000.table
  base := (110978221579827266265994013/2500000000000000000000000)
  polynomial :=
    { denominator := 607760000000000000000000000000000000000000000
      center := (3138047)
      previous := (0)
      next := (2757225)
      square := (120435796778568228957428941929600000000000000)
      linear := (-480654035212435665158636767800000000000000000)
      constant := (26979249578942327738328208536352000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree001.table
  base := (64908079227034530651460776778625270146137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-3468999309746087693612711104829026800000000000000)
      constant := (91558890414293994588692990537161399574791374112792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree001.table
  base := (2595848216056130443932232289292936522137/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-4625583320904738941960609450067722400000000000000)
      constant := (122057225467965846971276941087489419849721897626400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4989556882891020407/10000000000000000000)
  directionHi := (49895568828910204071/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree002.table
  base := (15899157659714230199584011932837966018071/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-4199352090360520076067799565925603600000000000000)
      constant := (58748767236139182786291699830584897689703065102340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree002.table
  base := (158939681737355043306867877292375127032037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-5599637936300604135711055375158844800000000000000)
      constant := (78309264524701913640162728856066485103631516169064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4989556882891020407/10000000000000000000)
  centralHi := (49895568828910204071/100000000000000000000)
  directionLo := (70562990140165057963/100000000000000000000)
  directionHi := (17640747535041264491/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree003.table
  base := (20496900924815109125178848186772759695513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-4929704870974952458522888027022180400000000000000)
      constant := (41610201432442088099276409861863728893766582404510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree003.table
  base := (102440760878002250061261255384901982427693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-6573692551696469329461501300249967200000000000000)
      constant := (55462775332134329123593190507919125559941493827496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70562990140165057963/100000000000000000000)
  centralHi := (17640747535041264491/25000000000000000000)
  directionLo := (21605415071055605011/25000000000000000000)
  directionHi := (17284332056844484009/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree004.table
  base := (17365273641105921051240330640859292806621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-5660057651589384840977976488118757200000000000000)
      constant := (32992375503380480171095748189074322475809975247736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree004.table
  base := (34713474399896450604298844906844171897273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-7547747167092334523211947225341089600000000000000)
      constant := (43978207761630088860065071749169362178328318506512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21605415071055605011/25000000000000000000)
  centralHi := (17284332056844484009/20000000000000000000)
  directionLo := (4989556882891020407/5000000000000000000)
  directionHi := (99791137657820408141/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree005.table
  base := (49104543186457635711547875086252005426569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-6390410432203817223433064949215334000000000000000)
      constant := (29149577014223154899851582677007861109555336396326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree005.table
  base := (49078149547263313889684129303755529166151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-8521801782488199716962393150432212000000000000000)
      constant := (38859758266046178632124315209880466020453342158072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4989556882891020407/5000000000000000000)
  centralHi := (99791137657820408141/100000000000000000000)
  directionLo := (111569883677462790327/100000000000000000000)
  directionHi := (13946235459682848791/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree006.table
  base := (35728747385647432297051700999498031988623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-7120763212818249605888153410311910800000000000000)
      constant := (28112785483824038382517449495808521677318827012842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree006.table
  base := (17853915846119638891417518196811228737499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-9495856397884064910712839075523334400000000000000)
      constant := (37481868440286594457708675462558510218377134769456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111569883677462790327/100000000000000000000)
  centralHi := (13946235459682848791/12500000000000000000)
  directionLo := (122218684056747614613/100000000000000000000)
  directionHi := (61109342028373807307/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree007.table
  base := (26327118744485680093717926695892439973103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-7851115993432681988343241871408487600000000000000)
      constant := (28840860070447023677847168522792151003693693246762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree007.table
  base := (26309844955432550318731861563099846295039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-10469911013279930104463285000614456800000000000000)
      constant := (38456552790476889452523259560843830745272124135608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122218684056747614613/100000000000000000000)
  centralHi := (61109342028373807307/50000000000000000000)
  directionLo := (66005633322701345687/50000000000000000000)
  directionHi := (1056090133163221531/800000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree008.table
  base := (4823650624869135969168211410395231217819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-8581468774047114370798330332505064400000000000000)
      constant := (30777992051565329362050931324513711027714572495304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree008.table
  base := (9639849858106469418287294469649328586451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-11443965628675795298213730925705579200000000000000)
      constant := (41042993955006617400774384438381147785821197959344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66005633322701345687/50000000000000000000)
  centralHi := (1056090133163221531/800000000000000000)
  directionLo := (141125980280330115927/100000000000000000000)
  directionHi := (17640747535041264491/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree009.table
  base := (13761097946945198879631137638533859649637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-9311821554661546753253418793601641200000000000000)
      constant := (33622877339880495597740415617342944417006479117198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree009.table
  base := (429617467087106365331728227496693915551/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-12418020244071660491964176850796701600000000000000)
      constant := (44839667237047043442718767765627573580219999835904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141125980280330115927/100000000000000000000)
  centralHi := (17640747535041264491/12500000000000000000)
  directionLo := (14968670648673061221/10000000000000000000)
  directionHi := (149686706486730612211/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree010.table
  base := (9243542741992119931369964492156031472619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-10042174335275979135708507254698218000000000000000)
      constant := (37208237988916340827089121919057712953365631603026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree010.table
  base := (9231284930077786864179551518328297698521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-13392074859467525685714622775887824000000000000000)
      constant := (49623685260252766804428583909505957957169597512712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14968670648673061221/10000000000000000000)
  centralHi := (149686706486730612211/100000000000000000000)
  directionLo := (78891821324528241513/50000000000000000000)
  directionHi := (157783642649056483027/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree011.table
  base := (5464116315444392793610052585424896410241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-10772527115890411518163595715794794800000000000000)
      constant := (41437868498925714865677209507123525861219685175414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree011.table
  base := (2726332669850618467110795862497001754391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-14366129474863390879465068700978946400000000000000)
      constant := (55266870173837376464976681066546031978426235518704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78891821324528241513/50000000000000000000)
  centralHi := (157783642649056483027/100000000000000000000)
  directionLo := (10342805031677983071/6250000000000000000)
  directionHi := (165484880506847729137/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree012.table
  base := (2255067592398473208092926385209694321369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-11502879896504843900618684176891371600000000000000)
      constant := (46253678945025580980280290673726772692970807435526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree012.table
  base := (112213730616507638145802185068988768423/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-15340184090259256073215514626070068800000000000000)
      constant := (61691826695234915839904504329888622559547409121120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10342805031677983071/6250000000000000000)
  centralHi := (165484880506847729137/100000000000000000000)
  directionLo := (172843320568444840089/100000000000000000000)
  directionHi := (17284332056844484009/10000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree013.table
  base := (-245631634533515193825219905665597661033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-12233232677119276283073772637987948400000000000000)
      constant := (51618388182318779939985447023395570952340376906036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree013.table
  base := (-125368883379915783766157363634693178927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-16314238705655121266965960551161191200000000000000)
      constant := (68848879671795896123572333989725502971020702107424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172843320568444840089/100000000000000000000)
  centralHi := (17284332056844484009/10000000000000000000)
  directionLo := (22487628978884806607/12500000000000000000)
  directionHi := (179901031831078452857/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree014.table
  base := (-2848824410172696621254657998026243641837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-12963585457733708665528861099084525200000000000000)
      constant := (57506388971202146340000902361121189490328219224002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree014.table
  base := (-1429247444656524864221164559979649278177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-17288293321050986460716406476252313600000000000000)
      constant := (76703903824050665913100537859326682038123805561712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22487628978884806607/12500000000000000000)
  centralHi := (179901031831078452857/100000000000000000000)
  directionLo := (23336515459497435133/12500000000000000000)
  directionHi := (37338424735195896213/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree015.table
  base := (-2435946075635547177890877233354319507903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-13693938238348141047983949560181102000000000000000)
      constant := (63898886157164621078946096020249944344050490308076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree015.table
  base := (-2440520465843675407972618787711640732329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-18262347936446851654466852401343436000000000000000)
      constant := (85231847646415580371101820002966370333412873143024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23336515459497435133/12500000000000000000)
  centralHi := (37338424735195896213/20000000000000000000)
  directionLo := (48311176780978781791/25000000000000000000)
  directionHi := (38648941424783025433/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree016.table
  base := (-6602643621006474071810357918492765925047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-14424291018962573430439038021277678800000000000000)
      constant := (70781274371888084830413658799690309463163444586662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree016.table
  base := (-6611282880498595150394520252295433888379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-19236402551842716848217298326434558400000000000000)
      constant := (94413240966074785381127535256145012317869072375912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48311176780978781791/25000000000000000000)
  centralHi := (38648941424783025433/20000000000000000000)
  directionLo := (199582275315640816281/100000000000000000000)
  directionHi := (99791137657820408141/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree017.table
  base := (-8075326977946165171314714556384602021471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-15154643799577005812894126482374255600000000000000)
      constant := (78141693941986227375543988382480380705783575546166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree017.table
  base := (-8083466775671344973834038555794880583411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-20210457167238582041967744251525680800000000000000)
      constant := (104232271863389588828111472314221557585222871447208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199582275315640816281/100000000000000000000)
  centralHi := (99791137657820408141/50000000000000000000)
  directionLo := (102862350265936424749/50000000000000000000)
  directionHi := (205724700531872849499/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree018.table
  base := (-9318630485292877192557005182163600965217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-15884996580191438195349214943470832400000000000000)
      constant := (85970210510523163745140296856465074173884027729482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree018.table
  base := (-9326281573024310641860563552658831610597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-21184511782634447235718190176616803200000000000000)
      constant := (114675694209320758877530051301795705039711008062616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102862350265936424749/50000000000000000000)
  centralHi := (205724700531872849499/100000000000000000000)
  directionLo := (21168897042049517389/10000000000000000000)
  directionHi := (211688970420495173891/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree019.table
  base := (-2589272125116108235296539840803260937959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-16615349360805870577804303404567409200000000000000)
      constant := (94258328161867507483434085232859479432629855570456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree019.table
  base := (-2072852694528632919006843547282730655567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-22158566398030312429468636101707925600000000000000)
      constant := (125732179265571892855187151429415610222310721403880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21168897042049517389/10000000000000000000)
  centralHi := (211688970420495173891/100000000000000000000)
  directionLo := (217489742255697650803/100000000000000000000)
  directionHi := (54372435563924412701/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree020.table
  base := (-2242392852994598190858137190273804496327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-17345702141420302960259391865663986000000000000000)
      constant := (102998683723515467612731146297213664759388335727710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree020.table
  base := (-11218677824998516478862690695788447412829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-23132621013426177623219082026799048000000000000000)
      constant := (137391908495066277900601366220529647748327961975512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217489742255697650803/100000000000000000000)
  centralHi := (54372435563924412701/25000000000000000000)
  directionLo := (111569883677462790327/50000000000000000000)
  directionHi := (44627953470985116131/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree021.table
  base := (-11901841472299654098164444068684756266527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-18076054922034735342714480326760562800000000000000)
      constant := (112184841914149250105453343452176267708610086274742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree021.table
  base := (-5954055130527465446363657487129664769533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-24106675628822042816969527951890170400000000000000)
      constant := (149646300628147818447407772688104291113332507184048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111569883677462790327/50000000000000000000)
  centralHi := (44627953470985116131/20000000000000000000)
  directionLo := (228650221001360126519/100000000000000000000)
  directionHi := (5716255525034003163/2500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree022.table
  base := (-12443047885545979975004031261770670552521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-18806407702649167725169568787857139600000000000000)
      constant := (121811148650582664537659274322466464333165282149466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree022.table
  base := (-12448890120457978649455431763121192757707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-25080730244217908010719973876981292800000000000000)
      constant := (162487816159320479384166533904964014716910882398696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228650221001360126519/100000000000000000000)
  centralHi := (5716255525034003163/2500000000000000000)
  directionLo := (117015481190237540991/50000000000000000000)
  directionHi := (234030962380475081983/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree023.table
  base := (-3212494328210022437198729165018105856339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-19536760483263600107624657248953716400000000000000)
      constant := (131872619552039467453790058295722050708846937072376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree023.table
  base := (-12855412370616898385550290754337376404823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-26054784859613773204470419802072415200000000000000)
      constant := (175909808712291472958511642810700049123480766443144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117015481190237540991/50000000000000000000)
  centralHi := (234030962380475081983/100000000000000000000)
  directionLo := (59822685465826767457/25000000000000000000)
  directionHi := (239290741863307069829/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree024.table
  base := (-13135346290071416963682703557270491786227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-20267113263878032490079745710050293200000000000000)
      constant := (142364851054399343175774861947683693880511326130942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree024.table
  base := (-1314039430065175866509200108029123230519/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-27028839475009638398220865727163537600000000000000)
      constant := (189906406520455624072720202387464331036994012138320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59822685465826767457/25000000000000000000)
  centralHi := (239290741863307069829/100000000000000000000)
  directionLo := (122218684056747614613/50000000000000000000)
  directionHi := (244437368113495229227/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree025.table
  base := (-1663800746483438786510069324709726818691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-20997466044492464872534834171146870000000000000000)
      constant := (153283947035222912183131323563327002965174341506288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree025.table
  base := (-13315087454629857060750337950708837159967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-28002894090405503591971311652254660000000000000000)
      constant := (204472414574083480441722047608119327907882129083976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122218684056747614613/50000000000000000000)
  centralHi := (244437368113495229227/100000000000000000000)
  directionLo := (249477844144551020351/100000000000000000000)
  directionHi := (3898091314758609693/1562500000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree026.table
  base := (-13385121267946119701162082516481197914959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-21727818825106897254989922632243446800000000000000)
      constant := (164626456781259584698868276386214897816356654334614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree026.table
  base := (-13389456821526278516923939993202616961377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-28976948705801368785721757577345782400000000000000)
      constant := (219603231885579933719191056162287261758566004950456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249477844144551020351/100000000000000000000)
  centralHi := (3898091314758609693/1562500000000000000)
  directionLo := (127209239550212512683/50000000000000000000)
  directionHi := (254418479100425025367/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree027.table
  base := (-208880073036706168114661741558093431893/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-22458171605721329637445011093340023600000000000000)
      constant := (176389321718775024971693822598849570590021281444992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree027.table
  base := (-6686167360613542183433239797240037533711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-29951003321197233979472203502436904800000000000000)
      constant := (235294780437966400087635326058940588491664832931216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127209239550212512683/50000000000000000000)
  centralHi := (254418479100425025367/100000000000000000000)
  directionLo := (129632490426333630067/50000000000000000000)
  directionHi := (51852996170533452027/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree028.table
  base := (-6633924852670035640221426060536697738221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-23188524386335762019900099554436600400000000000000)
      constant := (188569829207892624020424358562472760806723259283332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree028.table
  base := (-265431085749027538527949785977765303613/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-30925057936593099173222649427528027200000000000000)
      constant := (251543443553777151849710411926453256144508056113200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129632490426333630067/50000000000000000000)
  centralHi := (51852996170533452027/20000000000000000000)
  directionLo := (66005633322701345687/25000000000000000000)
  directionHi := (264022533290805382749/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree029.table
  base := (-13090647373791640360788593780022604722239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-23918877166950194402355188015533177200000000000000)
      constant := (201165572207012920034589479819625920570892201749494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree029.table
  base := (-818379124586295607723574070328141007369/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-31899112551988964366973095352619149600000000000000)
      constant := (268346012093396630078519991493315614378452290570112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66005633322701345687/25000000000000000000)
  centralHi := (264022533290805382749/100000000000000000000)
  directionLo := (268695861289404590271/100000000000000000000)
  directionHi := (4198372832646946723/1562500000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree030.table
  base := (-128428882935480938109559703969577693471/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-24649229947564626784810276476629754000000000000000)
      constant := (214174413916148804523607462063841831665042845816600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree030.table
  base := (-12846039792942679340655277078376276235201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-32873167167384829560723541277710272000000000000000)
      constant := (285699637294868954752700689532735587299717034310328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268695861289404590271/100000000000000000000)
  centralHi := (4198372832646946723/1562500000000000000)
  directionLo := (273289285671457430807/100000000000000000000)
  directionHi := (34161160708932178851/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree031.table
  base := (-3132513105587659029175546826002724332941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-25379582728179059167265364937726330800000000000000)
      constant := (227594456700166005936416549155706608785625382875144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree031.table
  base := (-3133238724137636859679565871493551778481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-33847221782780694754473987202801394400000000000000)
      constant := (303601789323067793829080461653807985227410245352672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273289285671457430807/100000000000000000000)
  centralHi := (34161160708932178851/12500000000000000000)
  directionLo := (55561353997747745093/20000000000000000000)
  directionHi := (138903384994369362733/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree032.table
  base := (-6078504044350105869350840819234052505949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-26109935508793491549720453398822907600000000000000)
      constant := (241424014722851025080078847810503531523330213770308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree032.table
  base := (-6079839412610601230961714901807242793837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-34821276398176559948224433127892516800000000000000)
      constant := (322050220769202878177377009991632460003747019242672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55561353997747745093/20000000000000000000)
  centralHi := (138903384994369362733/50000000000000000000)
  directionLo := (141125980280330115927/50000000000000000000)
  directionHi := (56450392112132046371/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree033.table
  base := (-2345616335165006692602996401217697490121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-26840288289407923932175541859919484400000000000000)
      constant := (255661589816297119076151996947978718870506494395330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree033.table
  base := (-11730537116905978762506428561154121207387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-35795331013572425141974879052983639200000000000000)
      constant := (341042934466342461134384906430288594342810342885736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141125980280330115927/50000000000000000000)
  centralHi := (56450392112132046371/20000000000000000000)
  directionLo := (286628220922324769219/100000000000000000000)
  directionHi := (14331411046116238461/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree034.table
  base := (-11247119130255824297702471974090842195299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-27570641070022356314630630321016061200000000000000)
      constant := (270305850181317890252118552924760102782316333820254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree034.table
  base := (-2812343713303291840240406591269683864393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-36769385628968290335725324978074761600000000000000)
      constant := (360578155081585908414121436917595162556791099560416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286628220922324769219/100000000000000000000)
  centralHi := (14331411046116238461/5000000000000000000)
  directionLo := (58187732321463612841/20000000000000000000)
  directionHi := (145469330803659032103/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree035.table
  base := (-10717540298954666395674343525374676418819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-28300993850636788697085718782112638000000000000000)
      constant := (285355611571235616506790559578630184281529749622174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree035.table
  base := (-10719611011099051338540394518699304100859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-37743440244364155529475770903165884000000000000000)
      constant := (380654304021057888041617626451870942970861171381352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58187732321463612841/20000000000000000000)
  centralHi := (145469330803659032103/50000000000000000000)
  directionLo := (29518616601497104333/10000000000000000000)
  directionHi := (295186166014971043331/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree036.table
  base := (-10142386964651880187412645467672709300611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-29031346631251221079540807243209214800000000000000)
      constant := (300809820657894776740012634717304272263718596776606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree036.table
  base := (-5072143254873588058982654914004750295509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-38717494859760020723226216828257006400000000000000)
      constant := (401269977245930439324096765502595675416033963373104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29518616601497104333/10000000000000000000)
  centralHi := (295186166014971043331/100000000000000000000)
  directionLo := (299373412973461224421/100000000000000000000)
  directionHi := (149686706486730612211/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree037.table
  base := (-4762182668168538789785751936218532138769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-29761699411865653461995895704305791600000000000000)
      constant := (316667540317780575321793342019030260273161294129748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree037.table
  base := (-9526106710076131535762141773247232751719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-39691549475155885916976662753348128800000000000000)
      constant := (422423925649751177385330922879192015656792753447432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299373412973461224421/100000000000000000000)
  centralHi := (149686706486730612211/50000000000000000000)
  directionLo := (303502896500410811071/100000000000000000000)
  directionHi := (4742232757818918923/1562500000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree038.table
  base := (-8865883655870871944814650429406508030347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-30492052192480085844450984165402368400000000000000)
      constant := (332927936609358726085047977302561082609648612980462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree038.table
  base := (-554217439266742379559998170938401427641/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-40665604090551751110727108678439251200000000000000)
      constant := (444115037691702831140328505893820483633464757866368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303502896500410811071/100000000000000000000)
  centralHi := (4742232757818918923/1562500000000000000)
  directionLo := (153788471587518217769/50000000000000000000)
  directionHi := (307576943175036435539/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree039.table
  base := (-8169085499170518273745700123517474855343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-31222404973094518226906072626498945200000000000000)
      constant := (349590267241325963001666611415181838025309109576278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree039.table
  base := (-8170546242132888455913479714520064977101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-41639658705947616304477554603530373600000000000000)
      constant := (466342324018545802609792080516104092299640138013528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153788471587518217769/50000000000000000000)
  centralHi := (307576943175036435539/100000000000000000000)
  directionLo := (311597727465493734041/100000000000000000000)
  directionHi := (155798863732746867021/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree040.table
  base := (-7435879279045353431100294518389493254221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-31952757753708950609361161087595522000000000000000)
      constant := (366653871356177772630668461392411704590138889377666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree040.table
  base := (-7437215997695640046800916946388914906781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-42613713321343481498228000528621496000000000000000)
      constant := (489104903840977020509785674349909552736030755940568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311597727465493734041/100000000000000000000)
  centralHi := (155798863732746867021/50000000000000000000)
  directionLo := (315567285298112966053/100000000000000000000)
  directionHi := (157783642649056483027/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree041.table
  base := (-1666991098689547801789692054807969606907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-32683110534323382991816249548692098800000000000000)
      constant := (384118160474969504970555050497879258615537604248888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree041.table
  base := (-6669186961336203800746205367611066006091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-43587767936739346691978446453712618400000000000000)
      constant := (512401992858786773123884945522677445118787740278248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315567285298112966053/100000000000000000000)
  centralHi := (157783642649056483027/50000000000000000000)
  directionLo := (4991992595451466647/1562500000000000000)
  directionHi := (319487526108893865409/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree042.table
  base := (-2933427209690842493301511046246751135371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-33413463314937815374271338009788675600000000000000)
      constant := (401982610467848960996373785362562392680623804871132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree042.table
  base := (-5867972008775221071744839528286627487671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-44561822552135211885728892378803740800000000000000)
      constant := (536232892554150202333315415981433779895567307588488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4991992595451466647/1562500000000000000)
  centralHi := (319487526108893865409/100000000000000000000)
  directionLo := (80840060894932244183/25000000000000000000)
  directionHi := (323360243579728976733/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree043.table
  base := (-5033897668877393768293646181330670974239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-34143816095552247756726426470885252400000000000000)
      constant := (420246754431262940842097442220068802546890051341494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree043.table
  base := (-2517459397506511990938680190942738732987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-45535877167531077079479338303894863200000000000000)
      constant := (560596980694172267632240331553940072948947943845072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80840060894932244183/25000000000000000000)
  centralHi := (323360243579728976733/100000000000000000000)
  directionLo := (163593562615328915721/50000000000000000000)
  directionHi := (327187125230657831443/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree044.table
  base := (-2085147727806394193562796157745643022823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-34874168876166680139181514931981829200000000000000)
      constant := (438910176367011566687361828738774275687353564520716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree044.table
  base := (-4171228008091197457208260277632284717927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-46509931782926942273229784228985985600000000000000)
      constant := (585493702902847261489210725265632137345480891918856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163593562615328915721/50000000000000000000)
  centralHi := (327187125230657831443/100000000000000000000)
  directionLo := (330969761013695458273/100000000000000000000)
  directionHi := (165484880506847729137/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree045.table
  base := (-1638559146478331033353399217923159555103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-35604521656781112521636603393078406000000000000000)
      constant := (457972505570816399532504523002882541666374329050476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree045.table
  base := (-3277969573444727378322852746943183205117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-47483986398322807466980230154077108000000000000000)
      constant := (610922565179261949680055989560146892247903572553176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330969761013695458273/100000000000000000000)
  centralHi := (165484880506847729137/50000000000000000000)
  directionLo := (334709651032388370981/100000000000000000000)
  directionHi := (167354825516194185491/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree046.table
  base := (-2355320285982013882113377381686317089053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-36334874437395544904091691854174982800000000000000)
      constant := (477433411649014967116672138117171805114912234411938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree046.table
  base := (-2356097043980025143394119862021025494817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-48458041013718672660730676079168230400000000000000)
      constant := (636883127253476782075524785716966073943941634254776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334709651032388370981/100000000000000000000)
  centralHi := (167354825516194185491/50000000000000000000)
  directionLo := (67681642498681639867/20000000000000000000)
  directionHi := (42301026561676024917/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree047.table
  base := (-21964873680919766024624102569248539397/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-37065227218009977286546780315271559600000000000000)
      constant := (497292600091595669237222282613156374166242148592768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree047.table
  base := (-1406460383269395802610850142518981111259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-49432095629114537854481122004259352800000000000000)
      constant := (663374996684329781757702223593387541921052188552552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67681642498681639867/20000000000000000000)
  centralHi := (42301026561676024917/12500000000000000000)
  directionLo := (17103339299077258913/5000000000000000000)
  directionHi := (342066785981545178261/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree048.table
  base := (-53646424867382038735597337071766475011/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-37795579998624409669001868776368136400000000000000)
      constant := (517549808338215781501361330952097315550818889592048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree048.table
  base := (-107454331224208396307633435273369335589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-50406150244510403048231567929350475200000000000000)
      constant := (690397823614653111296180250765540212331448262339168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17103339299077258913/5000000000000000000)
  centralHi := (342066785981545178261/100000000000000000000)
  directionLo := (345686641136889680179/100000000000000000000)
  directionHi := (17284332056844484009/5000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree049.table
  base := (573745212010088205133529687403907972691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-38525932779238842051456957237464713200000000000000)
      constant := (538204802281250670994703051320617236157605495227714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree049.table
  base := (573156530407995039265013188866742623131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-51380204859906268241982013854441597600000000000000)
      constant := (717951296109272109338532790789108207891992923156632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345686641136889680179/100000000000000000000)
  centralHi := (17284332056844484009/5000000000000000000)
  directionLo := (349268981802371428491/100000000000000000000)
  directionHi := (87317245450592857123/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree050.table
  base := (1602395051449568642734102344584717040577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-39256285559853274433912045698561290000000000000000)
      constant := (559257373156433638444103022076741577766574783443958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree050.table
  base := (200232342128094867481816121317944733407/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-52354259475302133435732459779532720000000000000000)
      constant := (746035136009843319487870294191196273808527843933632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349268981802371428491/100000000000000000000)
  centralHi := (87317245450592857123/25000000000000000000)
  directionLo := (352814950700825289817/100000000000000000000)
  directionHi := (176407475350412644909/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree051.table
  base := (106249618142461194654231148620471256599/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-39986638340467706816367134159657866800000000000000)
      constant := (580707334777375181784435793176211487981414795248650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree051.table
  base := (2655752019817928995616210750559472892549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-53328314090697998629482905704623842400000000000000)
      constant := (774649095248231402079262429876626843628759888308328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352814950700825289817/100000000000000000000)
  centralHi := (176407475350412644909/50000000000000000000)
  directionLo := (71265126738619161809/20000000000000000000)
  directionHi := (178162816846547904523/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree052.table
  base := (1867400923905645834751153371751698301879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-40716991121082139198822222620754443600000000000000)
      constant := (602554521075295403722969789730028452346871000894132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree052.table
  base := (3734357170940447088575075713883892564313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-54302368706093863823233351629714964800000000000000)
      constant := (803792952566854908139368570565762740431750554288136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71265126738619161809/20000000000000000000)
  centralHi := (178162816846547904523/50000000000000000000)
  directionLo := (359802063662156905713/100000000000000000000)
  directionHi := (179901031831078452857/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree053.table
  base := (75588303699933719143944734011998059593/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-41447343901696571581277311081851020400000000000000)
      constant := (624798783909748555727907121273569887696725801806208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree053.table
  base := (2418623364608347171283955529143892584719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-55276423321489729016983797554806087200000000000000)
      constant := (833466510600360867359012684143228904633784632257136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359802063662156905713/100000000000000000000)
  centralHi := (179901031831078452857/50000000000000000000)
  directionLo := (2837853312989265191/781250000000000000)
  directionHi := (363245224062625944449/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree054.table
  base := (1192881513830785500169729247353688236093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-42177696682311003963732399542947597200000000000000)
      constant := (647439991120038172339250793027654072315490798921110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree054.table
  base := (5964039354579740600168379629369474790951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-56250477936885594210734243479897209600000000000000)
      constant := (863669593278216552582353666529817060441601084103672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2837853312989265191/781250000000000000)
  centralHi := (363245224062625944449/100000000000000000000)
  directionLo := (366656052170242843839/100000000000000000000)
  directionHi := (1145800163032008887/312500000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree055.table
  base := (2223353040631650167178752755627065809/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-42908049462925436346187488004044174000000000000000)
      constant := (670478024790479284787656511282497900529354404115200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree055.table
  base := (444649676251772298962294363250046507929/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-57224532552281459404484689404988332000000000000000)
      constant := (894402043512419549581317778263750403688737414267008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366656052170242843839/100000000000000000000)
  centralHi := (1145800163032008887/312500000000000000)
  directionLo := (185017721030870687263/50000000000000000000)
  directionHi := (370035442061741374527/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree056.table
  base := (8288314080325615245443829095727200113243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-43638402243539868728642576465140750800000000000000)
      constant := (693912779705716993633386332190571781078563316910322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree056.table
  base := (8288009552388764876241519103047829389273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-58198587167677324598235135330079454400000000000000)
      constant := (925663721138599355535974703517498487775477777077256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185017721030870687263/50000000000000000000)
  centralHi := (370035442061741374527/100000000000000000000)
  directionLo := (23336515459497435133/6250000000000000000)
  directionHi := (373384247351958962129/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree057.table
  base := (189697789680183001499212388527148884439/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-44368755024154301111097664926237327600000000000000)
      constant := (717744161975007298161855033213950085096121854465300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree057.table
  base := (4742306330478205778466612614625937866499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-59172641783073189791985581255170576800000000000000)
      constant := (957454501082380635337725096090437222210571370945456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23336515459497435133/6250000000000000000)
  centralHi := (373384247351958962129/100000000000000000000)
  directionLo := (188351641855964046183/50000000000000000000)
  directionHi := (376703283711928092367/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree058.table
  base := (1338026746143036657518694300347828120063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-45099107804768733493552753387333904400000000000000)
      constant := (741972087806749425076564631562441950530384820212816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree058.table
  base := (10703962399978164137771564479357519096527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-60146696398469054985736027180261699200000000000000)
      constant := (989774271726057226482815337668652607114898158060344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188351641855964046183/50000000000000000000)
  centralHi := (376703283711928092367/100000000000000000000)
  directionLo := (379993331188995873947/100000000000000000000)
  directionHi := (94998332797248968487/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree059.table
  base := (597303578749839618350723623401503613809/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-45829460585383165876007841848430481200000000000000)
      constant := (766596482416666506865805727400872192493882080865720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree059.table
  base := (119458430170237217308108279244029256891/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-61120751013864920179486473105352821600000000000000)
      constant := (1022622933453437087935725733732776200722138593935200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379993331188995873947/100000000000000000000)
  centralHi := (94998332797248968487/25000000000000000000)
  directionLo := (191627568173834541829/50000000000000000000)
  directionHi := (383255136347669083659/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree060.table
  base := (13210269542474947358666350842113455180437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-46559813365997598258462930309527058000000000000000)
      constant := (791617279054896202462972351839234122260121458900398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree060.table
  base := (6605030972340853437169507098655453016723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-62094805629260785373236919030443944000000000000000)
      constant := (1056000397353205497215827257985943586647798960987312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191627568173834541829/50000000000000000000)
  centralHi := (383255136347669083659/100000000000000000000)
  directionLo := (48311176780978781791/12500000000000000000)
  directionHi := (386489414247830254329/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree061.table
  base := (14496635810170395023964384311925777454547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-47290166146612030640918018770623634800000000000000)
      constant := (817034418138903539525734502145576203785928226806338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree061.table
  base := (14496447297784110648652790722564407266767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-63068860244656650566987364955535066400000000000000)
      constant := (1089906584063355354319060660068743448288694101965624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48311176780978781791/12500000000000000000)
  centralHi := (386489414247830254329/100000000000000000000)
  directionLo := (38969685027517408867/10000000000000000000)
  directionHi := (389696850275174088671/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree062.table
  base := (61738346806318859168470763523742067827/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-48020518927226463023373107231720211600000000000000)
      constant := (842847846480590159720970998593606951082480464757248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree062.table
  base := (395121141064638388093556134683001377599/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-64042914860052515760737810880626188800000000000000)
      constant := (1124341422741183169046109285247298212393379879677120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38969685027517408867/10000000000000000000)
  centralHi := (389696850275174088671/100000000000000000000)
  directionLo := (392878101837137223233/100000000000000000000)
  directionHi := (196439050918568611617/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree063.table
  base := (535477354360623747747825321279625570111/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-48750871707840895405828195692816788400000000000000)
      constant := (869057516597269449757934037408114182595886930444608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree063.table
  base := (3427024001613024105952552611160673981983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-65016969475448380954488256805717311200000000000000)
      constant := (1159304850145076788456607143246458448166473019721880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392878101837137223233/100000000000000000000)
  centralHi := (196439050918568611617/50000000000000000000)
  directionLo := (198016899968104037061/50000000000000000000)
  directionHi := (396033799936208074123/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree064.table
  base := (18487289063765371812117808420837496477971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-49481224488455327788283284153913365200000000000000)
      constant := (895663386097325230543277524331808602765594066704834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree064.table
  base := (18487148112835459491035218727547791983573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-65991024090844246148238702730808433600000000000000)
      constant := (1194796809815852165770776067081911737868694827226856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198016899968104037061/50000000000000000000)
  centralHi := (396033799936208074123/100000000000000000000)
  directionLo := (199582275315640816281/50000000000000000000)
  directionHi := (399164550631281632563/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree065.table
  base := (19860948657236046811444411797747388882783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-50211577269069760170738372615009942000000000000000)
      constant := (922665417132389888905217979922555198483977946721482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree065.table
  base := (248260259801046823536842444869070050107/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-66965078706240111341989148655899556000000000000000)
      constant := (1230817251346754341019021352373308015855776570728320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199582275315640816281/50000000000000000000)
  centralHi := (399164550631281632563/100000000000000000000)
  directionLo := (40227093639664488389/10000000000000000000)
  directionHi := (402270936396644883891/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree066.table
  base := (1328509783196497828597795447661589298811/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-50941930049684192553193461076106518800000000000000)
      constant := (950063575908781145626041787276244870004633721699104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree066.table
  base := (10628020273789678193077687584235401472703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-67939133321635976535739594580990678400000000000000)
      constant := (1267366129732442408964722578941217444805996532440432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40227093639664488389/10000000000000000000)
  centralHi := (402270936396644883891/100000000000000000000)
  directionLo := (50669189673402925909/12500000000000000000)
  directionHi := (405353517387223407273/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree067.table
  base := (2834103193417500325917701473425436104181/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-51672282830298624935648549537203095600000000000000)
      constant := (977857832251738332244501615201924573615363304513392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree067.table
  base := (566818009252436724678460069658680469539/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-68913187937031841729490040506081800800000000000000)
      constant := (1304443404788347297874755423861825282056171483984320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50669189673402925909/12500000000000000000)
  centralHi := (405353517387223407273/100000000000000000000)
  directionLo := (204206416308936375661/50000000000000000000)
  directionHi := (408412832617872751323/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree068.table
  base := (24110877895819328617071237731046144683681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-52402635610913057318103637998299672400000000000000)
      constant := (1006048159216710790372633309295625476752882845157174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree068.table
  base := (24110782537663886580670695301048279246831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-69887242552427706923240486431172923200000000000000)
      constant := (1342049040632740273131698952050260776937582530303032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204206416308936375661/50000000000000000000)
  centralHi := (408412832617872751323/100000000000000000000)
  directionLo := (102862350265936424749/25000000000000000000)
  directionHi := (411449401063745698997/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree069.table
  base := (25570244093311309197816095083874113931339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-53132988391527489700558726459396249200000000000000)
      constant := (1034634532742583119809447178623148731895675381781906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree069.table
  base := (12785078827425894329564446028535412047731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-70861297167823572116990932356264045600000000000000)
      constant := (1380183005224692964748780665467914189520500391295664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102862350265936424749/25000000000000000000)
  centralHi := (411449401063745698997/100000000000000000000)
  directionLo := (207231861344048381791/50000000000000000000)
  directionHi := (414463722688096763583/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree070.table
  base := (10566743003837432377218456415712006121/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-53863341172141922083013814920492826000000000000000)
      constant := (1063616931342283579470418880395859088841260505431040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree070.table
  base := (6762695937995734146954809775432568112809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-71835351783219437310741378281355168000000000000000)
      constant := (1418845269951858529022302028871820683415456536476192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207231861344048381791/50000000000000000000)
  centralHi := (414463722688096763583/100000000000000000000)
  directionLo := (41745627940328804153/10000000000000000000)
  directionHi := (417456279403288041531/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree071.table
  base := (5710535294286628413703935682013687496997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48772740000000000000000000000000000000000000000
      center := (251763403)
      previous := (0)
      next := (221332175)
      square := (9664972691480100373833672589850400000000000000)
      linear := (-768925266940230344584069061712526800000000000000)
      constant := (15394300504601704441392123460251574528366142730890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree071.table
  base := (1427630274426355221656334289424054032199/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65030320000000000000000000000000000000000000000
      center := (335771029)
      previous := (0)
      next := (295023075)
      square := (12886630255306800498444896786467200000000000000)
      linear := (-1025484597163595809922420059245722400000000000000)
      constant := (20535715623417873240297218524076291648822382547360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41745627940328804153/10000000000000000000)
  centralHi := (417456279403288041531/100000000000000000000)
  directionLo := (420427535970227106057/100000000000000000000)
  directionHi := (210213767985113553029/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree072.table
  base := (1879727359305724318275250435261322077017/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-55324046733370786847923991842685979600000000000000)
      constant := (1122769729058439342147634653822551502166434109243488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree072.table
  base := (30075573442274680825525922522328973971041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-73783461014011167698242270131537412800000000000000)
      constant := (1497754600338135424310687453650165269090520115438152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420427535970227106057/100000000000000000000)
  centralHi := (210213767985113553029/50000000000000000000)
  directionLo := (423377940840990347781/100000000000000000000)
  directionHi := (211688970420495173891/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree073.table
  base := (3161970172276463253202357635179815802187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-56054399513985219230379080303782556400000000000000)
      constant := (1152940095731773105819233027887457564265125016748980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree073.table
  base := (31619643474996589280550309178361693534091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-74757515629407032891992716056628535200000000000000)
      constant := (1538001622798963358123722525673866391894473467337752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423377940840990347781/100000000000000000000)
  centralHi := (211688970420495173891/50000000000000000000)
  directionLo := (213153963474478723043/50000000000000000000)
  directionHi := (426307926948957446087/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree074.table
  base := (33184828916822097609742502742635485204963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-56784752294599651612834168764879133200000000000000)
      constant := (1183506422176638541842088119157835005186196100471202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree074.table
  base := (16592388083159454899285076644993449215281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-75731570244802898085743161981719657600000000000000)
      constant := (1578776858444164134685872467924031041885303306942864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213153963474478723043/50000000000000000000)
  centralHi := (426307926948957446087/100000000000000000000)
  directionLo := (42921791245039873557/10000000000000000000)
  directionHi := (429217912450398735571/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree075.table
  base := (6954196814461977663202296951728797511541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-57515105075214083995289257225975710000000000000000)
      constant := (1214468696183406721851077549921301872299777784828070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree075.table
  base := (17385468154220506155500382225427327756913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-76705624860198763279493607906810780000000000000000)
      constant := (1620080291017758509563249321414655569153032471350672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42921791245039873557/10000000000000000000)
  centralHi := (429217912450398735571/100000000000000000000)
  directionLo := (3375846104852438283/781250000000000000)
  directionHi := (17284332056844484009/4000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree076.table
  base := (18189067848265372301430323049113700861693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-58245457855828516377744345687072286800000000000000)
      constant := (1245826906846583184768673961814559761028424826813244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree076.table
  base := (36378092455128164644908828693785868209693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-77679679475594628473244053831901902400000000000000)
      constant := (1661911906000539660014780030049522478050194556531496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3375846104852438283/781250000000000000)
  centralHi := (17284332056844484009/4000000000000000000)
  directionLo := (217489742255697650803/50000000000000000000)
  directionHi := (434979484511395301607/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree077.table
  base := (38006255659876659673266501152293806137537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-58975810636442948760199434148168863600000000000000)
      constant := (1277581044425265721511128194251316199693531124023798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree077.table
  base := (38006216519123551550319567952331377483967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-78653734090990493666994499756993024800000000000000)
      constant := (1704271690424192165853468741180541561039144499044024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217489742255697650803/50000000000000000000)
  centralHi := (434979484511395301607/100000000000000000000)
  directionLo := (437831839562359489991/100000000000000000000)
  directionHi := (54728979945294936249/12500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree078.table
  base := (9913829709022827074102645450100844260303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-59706163417057381142654522609265440400000000000000)
      constant := (1309731100218572126919189388388432036805226315342248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree078.table
  base := (39655283412760268553856418604510650154979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-79627788706386358860744945682084147200000000000000)
      constant := (1747159632705357078434992377976564771063202971139288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437831839562359489991/100000000000000000000)
  centralHi := (54728979945294936249/12500000000000000000)
  directionLo := (440665732186336695043/100000000000000000000)
  directionHi := (110166433046584173761/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree079.table
  base := (41325302781106938643657445949722587580377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-60436516197671813525109611070362017200000000000000)
      constant := (1342277066454425765876367361324857611536913191313158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree079.table
  base := (41325270727119848954785614033316214293089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-80601843321782224054495391607175269600000000000000)
      constant := (1790575722497494512680798706784435983394343875355208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440665732186336695043/100000000000000000000)
  centralHi := (110166433046584173761/25000000000000000000)
  directionLo := (221740758156952694601/50000000000000000000)
  directionHi := (443481516313905389203/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree080.table
  base := (43016187446304377957381443715778129285047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-61166868978286245907564699531458594000000000000000)
      constant := (1375218936190261397452010525302653152240872480853338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree080.table
  base := (4301615844558797086301983827391919103059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-81575897937178089248245837532266392000000000000000)
      constant := (1834519950558627942440310508409704289792708822170480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221740758156952694601/50000000000000000000)
  centralHi := (443481516313905389203/100000000000000000000)
  directionLo := (111569883677462790327/25000000000000000000)
  directionHi := (446279534709851161309/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree081.table
  base := (447279549224939487711603813903679921581/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-61897221758900678290019787992555170800000000000000)
      constant := (1408556703224369234222867834795704274159528256377400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree081.table
  base := (5590991086013378478343796457852965941627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-82549952552573954441996283457357514400000000000000)
      constant := (1878992308633261706574961964960966954095960371420352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111569883677462790327/25000000000000000000)
  centralHi := (446279534709851161309/100000000000000000000)
  directionLo := (56132514932523979579/12500000000000000000)
  directionHi := (449060119460191836633/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree082.table
  base := (46460589211315268310345756325770666811807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-62627574539515110672474876453651747600000000000000)
      constant := (1442290362016733789423823578725721884627476131362378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree082.table
  base := (23230282741412656790287380488725612869097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-83524007167969819635746729382448636800000000000000)
      constant := (1923992789346947950182758678559093822358443643498768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56132514932523979579/12500000000000000000)
  centralHi := (449060119460191836633/100000000000000000000)
  directionLo := (451823592432226007423/100000000000000000000)
  directionHi := (3529871815876765683/781250000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree083.table
  base := (48214076021110507437263192666566644460037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-63357927320129543054929964914748324400000000000000)
      constant := (1476419907618347551621454619671069545264744957438798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree083.table
  base := (3013378410137441759545178444291463095567/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-84498061783365684829497175307539759200000000000000)
      constant := (1969521386112143825356432081563248013737162870387584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451823592432226007423/100000000000000000000)
  centralHi := (3529871815876765683/781250000000000000)
  directionLo := (454570265709409103933/100000000000000000000)
  directionHi := (227285132854704551967/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree084.table
  base := (3124275161540219443211519083717190717303/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-64088280100743975437385053375844901200000000000000)
      constant := (1510945335608089585299256427798374292197385157016992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree084.table
  base := (49988383180921353857316039326194967253557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-85472116398761550023247621232630881600000000000000)
      constant := (2015578093044146472638859678814261873230507163222504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454570265709409103933/100000000000000000000)
  centralHi := (227285132854704551967/50000000000000000000)
  directionLo := (228650221001360126519/50000000000000000000)
  directionHi := (457300442002720253039/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree085.table
  base := (25891778748160244203743384888374037205631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-64818632881358407819840141836941478000000000000000)
      constant := (1545866642036357260854093572411433652339204055644948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree085.table
  base := (51783539953334934989211867963105873805231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-86446171014157415216998067157722004000000000000000)
      constant := (2062162904886024064547673514212278965738779906187832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228650221001360126519/50000000000000000000)
  centralHi := (457300442002720253039/100000000000000000000)
  directionLo := (230007207520027416111/50000000000000000000)
  directionHi := (460014415040054832223/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree086.table
  base := (26799765283410276047529414663448098977723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-65548985661972840202295230298038054800000000000000)
      constant := (1581183823374726779558001069454092407616073445328484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree086.table
  base := (1674984834632462791207579831033966836833/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-87420225629553280410748513082813126400000000000000)
      constant := (2109275816941577763771683747750638035457834502834432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230007207520027416111/50000000000000000000)
  centralHi := (460014415040054832223/100000000000000000000)
  directionLo := (231356234967530289931/50000000000000000000)
  directionHi := (462712469935060579863/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree087.table
  base := (13859078173317396826797576492128859802931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-66279338442587272584750318759134631600000000000000)
      constant := (1616896876470996142972253640522809836688880459186696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree087.table
  base := (27718149179611573576548250287085857974293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-88394280244949145604498959007904248800000000000000)
      constant := (2156916825015473384290938710299208714053908123005392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231356234967530289931/50000000000000000000)
  centralHi := (462712469935060579863/100000000000000000000)
  directionLo := (465394883536728255481/100000000000000000000)
  directionHi := (232697441768364127741/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree088.table
  base := (28646947871645875658331154526868749468711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-67009691223201704967205407220231208400000000000000)
      constant := (1653005798509033757923580966693321863553868632281588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree088.table
  base := (28646941394434063103395899482040654527769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-89368334860345010798249404932995371200000000000000)
      constant := (2205085925359774224920566946961458012640693790776336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465394883536728255481/100000000000000000000)
  centralHi := (232697441768364127741/50000000000000000000)
  directionLo := (93612384952190032793/20000000000000000000)
  directionHi := (234030962380475081983/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree089.table
  base := (29586136225726003613566085459064147934999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-67740044003816137349660495681327785200000000000000)
      constant := (1689510586972917888717789380011211148293884452407092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree089.table
  base := (59172260745321168289843741818271491235853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-90342389475740875991999850858086493600000000000000)
      constant := (2253783114626189200017724572160130132595807484047016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93612384952190032793/20000000000000000000)
  centralHi := (234030962380475081983/50000000000000000000)
  directionLo := (117678463726292620171/25000000000000000000)
  directionHi := (94142770981034096137/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree090.table
  base := (30535718163381422215483052903029471363803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-68470396784430569732115584142424362000000000000000)
      constant := (1726411239614907487348273991476565252992131769649124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree090.table
  base := (61071425749926753697645182099863164614357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-91316444091136741185750296783177616000000000000000)
      constant := (2303008389823424114107697537347948447212698617360104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117678463726292620171/25000000000000000000)
  centralHi := (94142770981034096137/20000000000000000000)
  directionLo := (473350927947169449079/100000000000000000000)
  directionHi := (11833773198679236227/2500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree091.table
  base := (31495690785035420817389213952731418052251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-69200749565045002114570672603520938800000000000000)
      constant := (1763707754426834279353380178295165523143411171015908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree091.table
  base := (62991372014725417183310219125804109835871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-92290498706532606379500742708268738400000000000000)
      constant := (2352761748279089688369045371738072515241587054121912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473350927947169449079/100000000000000000000)
  centralHi := (11833773198679236227/2500000000000000000)
  directionLo := (475973390828948461067/100000000000000000000)
  directionHi := (118993347707237115267/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree092.table
  base := (64932103000265859513163194702136510110363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-69931102345659434497025761064617515600000000000000)
      constant := (1801400129614550006802667164523240595910052751922802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree092.table
  base := (64932094368765589973438009042089425658463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-93264553321928471573251188633359860800000000000000)
      constant := (2403043187605678612726730598345420935416221023146936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475973390828948461067/100000000000000000000)
  centralHi := (118993347707237115267/25000000000000000000)
  directionLo := (59822685465826767457/12500000000000000000)
  directionHi := (478581483726614139657/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree093.table
  base := (33446797994184539100618004318573300747103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-70661455126273866879480849525714092400000000000000)
      constant := (1839488363575102008524019373010181180909579697285524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree093.table
  base := (66893588192285314120431313494766394519167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-94238607937324336767001634558450983200000000000000)
      constant := (2453852705670176238191725796516949596471876500618424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59822685465826767457/12500000000000000000)
  centralHi := (478581483726614139657/100000000000000000000)
  directionLo := (120293860076774063447/25000000000000000000)
  directionHi := (481175440307096253789/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree094.table
  base := (68875856398657305842831348447473533725831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-71391807906888299261935937986810669200000000000000)
      constant := (1877972454876345365684003567360754627652767425193274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree094.table
  base := (34437924678961002194793036121083172172987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-95212662552720201960752080483542105600000000000000)
      constant := (2505190300566916226079766397238672061748947047514928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120293860076774063447/25000000000000000000)
  centralHi := (481175440307096253789/100000000000000000000)
  directionLo := (24187774398623804851/5000000000000000000)
  directionHi := (483755487972476097021/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree095.table
  base := (1771972013401782541924668470777322017411/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-72122160687502731644391026447907246000000000000000)
      constant := (1916852402238731116479573790375560318601015258023760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree095.table
  base := (70878874178198692109243238457347571126607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-96186717168116067154502526408633228000000000000000)
      constant := (2557055970593334144806881865013626205451260697442104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24187774398623804851/5000000000000000000)
  centralHi := (483755487972476097021/100000000000000000000)
  directionLo := (486321848092648395009/100000000000000000000)
  directionHi := (48632184809264839501/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree096.table
  base := (72902665099236459532681949314287912312043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-72852513468117164026846114909003822800000000000000)
      constant := (1956128204519037955214120928881592147089600311965522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree096.table
  base := (36451329679307866831844945563981212000717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-97160771783511932348252972333724350400000000000000)
      constant := (2609449714228309195317140245042681416603601427700048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486321848092648395009/100000000000000000000)
  centralHi := (48632184809264839501/10000000000000000000)
  directionLo := (122218684056747614613/25000000000000000000)
  directionHi := (488874736226990458453/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree097.table
  base := (4684200446156008462747974323642031551117/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-73582866248731596409301203370100399600000000000000)
      constant := (1995799860695839742117284413463381155139078810705888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree097.table
  base := (37473600977874426849153775316975291118393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-98134826398907797542003418258815472800000000000000)
      constant := (2662371530112817437703780969551835087562016016395792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell169.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122218684056747614613/25000000000000000000)
  centralHi := (488874736226990458453/100000000000000000000)
  directionLo := (61426795291958349453/12500000000000000000)
  directionHi := (786262979737066873/160000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree098.table
  base := (77012504018422111897902977679381050239333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (17875201613)
      previous := (0)
      next := (15714584425)
      square := (686213061095087126542190753879378400000000000000)
      linear := (-74313219029346028791756291831196976400000000000000)
      constant := (2035867369856523385016521691153857296402174475895182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree098.table
  base := (38506249669909277677730316981103108899327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (23839743059)
      previous := (0)
      next := (20946638325)
      square := (914950748126782835389587671839171200000000000000)
      linear := (-99108881014303662735753864183906595200000000000000)
      constant := (2715821417032649516275157680053312481370996772843888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell169.Kernel098
