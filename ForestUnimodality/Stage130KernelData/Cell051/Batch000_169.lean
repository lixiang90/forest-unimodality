import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell051.Parameters
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch000_049
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch050_099
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch100_149
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch150_199
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch050_099
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch100_149
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree000.table
  base := (344624792416002944889186211/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (138)
      previous := (69)
      next := (69)
      square := (774368632989967803359476760000000000000)
      linear := (23853464995722221259066842000000000000)
      constant := (689249584832005889778372422000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree000.table
  base := (344624792416002944889186211/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (138)
      previous := (69)
      next := (69)
      square := (774368632989967803359476760000000000000)
      linear := (23853464995722221259066842000000000000)
      constant := (689249584832005889778372422000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree001.table
  base := (391407408303579549820734643517932785898363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-16505864873057153223177753010313102000000000000)
      constant := (8846177571232420364339875158040180614624991618267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree001.table
  base := (390606208443003659448456459680435415816309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-16551872049464669685294847923316602000000000000)
      constant := (8828099392755252980134715883894281014624978965781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24991763065798337011/50000000000000000000)
  directionHi := (49983526131596674023/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree002.table
  base := (23259091525635126522195213779038023005701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-33550603588513852108319076379849782000000000000)
      constant := (5270545652221855164485760461556617844639983423090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree002.table
  base := (115869955509818840823583467441249959810117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-33642617941328885032553266205856782000000000000)
      constant := (5251408964180814727383968433629250005639982876106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24991763065798337011/50000000000000000000)
  centralHi := (49983526131596674023/100000000000000000000)
  directionLo := (35343690275267009619/50000000000000000000)
  directionHi := (70687380550534019239/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree003.table
  base := (73041574216092827137883785558190739812757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-50595342303970550993460399749386462000000000000)
      constant := (3336744435283261213129380519348699754653303403626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree003.table
  base := (145392025354701602385248622550542670775047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-50733363833193100379811684488396962000000000000)
      constant := (3321331132256790177955526347429471331363123752423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35343690275267009619/50000000000000000000)
  centralHi := (70687380550534019239/100000000000000000000)
  directionLo := (43287003400686050253/50000000000000000000)
  directionHi := (86574006801372100507/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree004.table
  base := (97474535398245395463833200955035473808009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-67640081019427249878601723118923142000000000000)
      constant := (2267426959900258684313847814545247612115995591081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree004.table
  base := (48480752116082906066832159944535184325111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-67824109725057315727070102770937142000000000000)
      constant := (2256193327916429478712424415607130677810483053998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43287003400686050253/50000000000000000000)
  centralHi := (86574006801372100507/100000000000000000000)
  directionLo := (19993410452638669609/20000000000000000000)
  directionHi := (49983526131596674023/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree005.table
  base := (17244748382532277679554482814443297994093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-84684819734883948763743046488459822000000000000)
      constant := (1660787673430252426494128344933174234896947639348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree005.table
  base := (68608062861807838172113223511917676217469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-84914855616921531074328521053477322000000000000)
      constant := (1652965516901253636428092706158136440687928136221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19993410452638669609/20000000000000000000)
  centralHi := (49983526131596674023/50000000000000000000)
  directionLo := (111766562185387262013/100000000000000000000)
  directionHi := (55883281092693631007/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree006.table
  base := (12835291443677272131424388598609940265343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-101729558450340647648884369857996502000000000000)
      constant := (1307738721387820830725570416921782214095304404348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree006.table
  base := (51070908798849565344711039718867503490361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-102005601508785746421586939336017502000000000000)
      constant := (1302437053744148248612912737142241038158276764249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111766562185387262013/100000000000000000000)
  centralHi := (55883281092693631007/50000000000000000000)
  directionLo := (122434134567480998037/100000000000000000000)
  directionHi := (61217067283740499019/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree007.table
  base := (19862646183473650853345652728264432179477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-2423965248281578500694401902602718000000000000)
      constant := (22429294110186774278612660290533085152916511114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree007.table
  base := (19761410774687568908482834407014126661621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-2430537702054080852425415461603218000000000000)
      constant := (22358288914736240221778999467360410940400814922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122434134567480998037/100000000000000000000)
  centralHi := (61217067283740499019/50000000000000000000)
  directionLo := (132243979794303124287/100000000000000000000)
  directionHi := (2066312184285986317/1562500000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree008.table
  base := (7893684493533179193839918787569511220687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-135819035881254045419167016597069862000000000000)
      constant := (976920771653252801395576429865219800448564012732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree008.table
  base := (31417255309401397762351860778165547232559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-136187093292514177116103775901097862000000000000)
      constant := (974793786958340448883415054521619717020665462031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132243979794303124287/100000000000000000000)
  centralHi := (2066312184285986317/1562500000000000000)
  directionLo := (141374761101068038477/100000000000000000000)
  directionHi := (70687380550534019239/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree009.table
  base := (5103097742456649691683815675891491740201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-152863774596710744304308339966606542000000000000)
      constant := (910354442130959171708721713347883827631532264045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree009.table
  base := (12694115723548605596848810626111509940451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-153277839184378392463362194183638042000000000000)
      constant := (909291108587437448277236569891728200136636010118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141374761101068038477/100000000000000000000)
  centralHi := (70687380550534019239/50000000000000000000)
  directionLo := (37487644598697505517/25000000000000000000)
  directionHi := (149950578394790022069/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree010.table
  base := (10395685071871674138633623573207174431759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-169908513312167443189449663336143222000000000000)
      constant := (882253679305624616011416060928727842904874909662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree010.table
  base := (20685118703073067317422656569997320242137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-170368585076242607810620612466178222000000000000)
      constant := (882090604172816996205265963575142686565999146233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37487644598697505517/25000000000000000000)
  centralHi := (149950578394790022069/100000000000000000000)
  directionLo := (158061788062390575133/100000000000000000000)
  directionHi := (79030894031195287567/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree011.table
  base := (16972183280493759136393037449369907573993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-186953252027624142074590986705679902000000000000)
      constant := (882899853967115205085653358863270783333244028937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree011.table
  base := (4220315501959750577061803960974848361631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-187459330968106823157879030748718402000000000000)
      constant := (883553705199735694480933955752580849444964702716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158061788062390575133/100000000000000000000)
  centralHi := (79030894031195287567/50000000000000000000)
  directionLo := (165776601877430468991/100000000000000000000)
  directionHi := (1295129702167425539/781250000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree012.table
  base := (862644851963126672960069750518974453181/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-203997990743080840959732310075216582000000000000)
      constant := (906518467209943972433122577104569028681312794064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree012.table
  base := (13723211578233821273169721325461928869259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-204550076859971038505137449031258582000000000000)
      constant := (907954725335750940825687866494217938242789892331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165776601877430468991/100000000000000000000)
  centralHi := (1295129702167425539/781250000000000000)
  directionLo := (173148013602744201013/100000000000000000000)
  directionHi := (86574006801372100507/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree013.table
  base := (1390220216270745749950947908550444961973/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-221042729458537539844873633444753262000000000000)
      constant := (949494698558232871929948125734772303719493606056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree013.table
  base := (11052232304563781679795540788710837798481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-221640822751835253852395867313798762000000000000)
      constant := (951707678289155410446517767631383281103024457329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173148013602744201013/100000000000000000000)
  centralHi := (86574006801372100507/50000000000000000000)
  directionLo := (90109083197983013383/50000000000000000000)
  directionHi := (180218166395966026767/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree014.table
  base := (8824507434843351609681717697735313148581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-4858927921918249770000305241107958000000000000)
      constant := (20600688104568040822227096807539888509334932821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree014.table
  base := (8763055164315555680062656869762357967527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-4872072829463254473462332359108958000000000000)
      constant := (20661927155610802271589877394661684279706615607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90109083197983013383/50000000000000000000)
  centralHi := (180218166395966026767/100000000000000000000)
  directionLo := (187021229767297022801/100000000000000000000)
  directionHi := (93510614883648511401/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree015.table
  base := (6836336855439943109719818626886331362427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-255132206889450937615156280183826622000000000000)
      constant := (1084658865885745732629168178012611458785570618843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree015.table
  base := (6781887092209938482908797452713356297021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-255822314535563684546912703878879122000000000000)
      constant := (1088467922541212540462115631684518961526208084189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187021229767297022801/100000000000000000000)
  centralHi := (93510614883648511401/50000000000000000000)
  directionLo := (9679268214619857509/5000000000000000000)
  directionHi := (193585364292397150181/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree016.table
  base := (5102712097361953932683156224946168455153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-272176945604907636500297603553363302000000000000)
      constant := (1173938078776358785270018380105576708085877519377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree016.table
  base := (202177468186108949354592297126407267937/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-272913060427427899894171122161419302000000000000)
      constant := (1178581656902605929807482812370738710190754460825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9679268214619857509/5000000000000000000)
  centralHi := (193585364292397150181/100000000000000000000)
  directionLo := (199934104526386696091/100000000000000000000)
  directionHi := (49983526131596674023/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree017.table
  base := (447747061329911895470820642341450701251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-289221684320364335385438926922899982000000000000)
      constant := (1276330289589468849806514626108100009920141218072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree017.table
  base := (707839068447742815195294135875464655799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-290003806319292115241429540443959482000000000000)
      constant := (1281837911210908731206276625516190708591685555955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199934104526386696091/100000000000000000000)
  centralHi := (49983526131596674023/25000000000000000000)
  directionLo := (206087357781393589127/100000000000000000000)
  directionHi := (25760919722674198641/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree018.table
  base := (560346290791115732414415027045272350379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-306266423035821034270580250292436662000000000000)
      constant := (1391095758624591457269121960798663470299452569644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree018.table
  base := (1101756498278831890651017662901245029831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-307094552211156330588687958726499662000000000000)
      constant := (1397499088832275007726353402911325316160234778958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206087357781393589127/100000000000000000000)
  centralHi := (25760919722674198641/12500000000000000000)
  directionLo := (42412428330320411543/20000000000000000000)
  directionHi := (53015535412900514429/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree019.table
  base := (263668083113434503612592471268879400393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-323311161751277733155721573661973342000000000000)
      constant := (1517641115353244864497833385454108116816771466148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree019.table
  base := (1021190593614108884445796864162217095761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-324185298103020545935946377009039842000000000000)
      constant := (1524973326250281566966283095561351156870290612849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42412428330320411543/20000000000000000000)
  centralHi := (53015535412900514429/25000000000000000000)
  directionLo := (217873139249454391927/100000000000000000000)
  directionHi := (27234142406181798991/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree020.table
  base := (238336567088858219168460350413856827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-340355900466734432040862897031510022000000000000)
      constant := (1655483785881676994561916261334216625186606936886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree020.table
  base := (-29081310696561216254618629389342119697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-341276043994884761283204795291580022000000000000)
      constant := (1663779221621376153882415599191301397669845995727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217873139249454391927/100000000000000000000)
  centralHi := (27234142406181798991/12500000000000000000)
  directionLo := (111766562185387262013/50000000000000000000)
  directionHi := (223533124370774524027/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree021.table
  base := (-938735961408074159099728110794832086211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-7293890595554921039306208579613198000000000000)
      constant := (36820972574406671482484003852797262820141194349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree021.table
  base := (-964792970707853546073134117391681607479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-7313607956872428094499249256614698000000000000)
      constant := (37010645968418331066637234544676319720006274361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111766562185387262013/50000000000000000000)
  centralHi := (223533124370774524027/100000000000000000000)
  directionLo := (45810658399769003547/20000000000000000000)
  directionHi := (28631661499855627217/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree022.table
  base := (-1777447746486390848660247047509988614711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-374445377897647829811145543770583382000000000000)
      constant := (1963545559193150596131183373600375513615166266601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree022.table
  base := (-1800387321290881338358881812780355017893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-375457535778613191977721631856660382000000000000)
      constant := (1973874338271988039220100430090248953767584075963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45810658399769003547/20000000000000000000)
  centralHi := (28631661499855627217/12500000000000000000)
  directionLo := (234443518699187260327/100000000000000000000)
  directionHi := (29305439837398407541/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree023.table
  base := (-1263835276596391687795859603279652903869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-391490116613104528696286867140120062000000000000)
      constant := (2133166134735401614173752657564714304463638572358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree023.table
  base := (-2547840127362117341597709061362538206327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-392548281670477407324980050139200562000000000000)
      constant := (2144566734466835684637744897632873238118022886057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234443518699187260327/100000000000000000000)
  centralHi := (29305439837398407541/12500000000000000000)
  directionLo := (11985628513411820049/5000000000000000000)
  directionHi := (239712570268236400981/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree024.table
  base := (-3199396579601621462272099199895855804111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-408534855328561227581428190509656742000000000000)
      constant := (2312863648936052087701856166639858890466626162001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree024.table
  base := (-643421999204374460918437925527994147267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-409639027562341622672238468421740742000000000000)
      constant := (2325373866054410574489162212179989840335719387985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11985628513411820049/5000000000000000000)
  centralHi := (239712570268236400981/100000000000000000000)
  directionLo := (122434134567480998037/50000000000000000000)
  directionHi := (9794730765398479843/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree025.table
  base := (-950238900968146189922066977502912639361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-425579594044017926466569513879193422000000000000)
      constant := (2502449923701728690282932415927504287151927579004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree025.table
  base := (-95412385497652698559151704352241965121/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-426729773454205838019496886704280922000000000000)
      constant := (2516108261712887263946595522847878303830952116440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122434134567480998037/50000000000000000000)
  centralHi := (9794730765398479843/4000000000000000000)
  directionLo := (124958815328991685057/50000000000000000000)
  directionHi := (49983526131596674023/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree026.table
  base := (-216965138239294025391923843463659825533/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-442624332759474625351710837248730102000000000000)
      constant := (2701767835429651511136315745075694956168911344060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree026.table
  base := (-1088230626944298044395080136764646219901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-443820519346070053366755304986821102000000000000)
      constant := (2716613453656880120407899420342932672457602119564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124958815328991685057/50000000000000000000)
  centralHi := (49983526131596674023/20000000000000000000)
  directionLo := (25486697510318632273/10000000000000000000)
  directionHi := (254866975103186322731/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree027.table
  base := (-4820252899581170076134279023168256019701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-459669071474931324236852160618266782000000000000)
      constant := (2910686021079405825108677436788940348744630531691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree027.table
  base := (-151005603514068272282838165083507047797/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-460911265237934268714013723269361282000000000000)
      constant := (2926758683933151654791223157676670138012945370464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25486697510318632273/10000000000000000000)
  centralHi := (254866975103186322731/100000000000000000000)
  directionLo := (259722020404116301519/100000000000000000000)
  directionHi := (3246525255051453769/1250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree028.table
  base := (-5248672757950389399088553219083216547959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-9728853269191592308612111918118438000000000000)
      constant := (63859072160508170617877829273673978759512434681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree028.table
  base := (-1051821604645790112469801179514049510691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-9755143084281601715536166154120438000000000000)
      constant := (64212950257133847935514067611219689497707553345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259722020404116301519/100000000000000000000)
  centralHi := (3246525255051453769/1250000000000000000)
  directionLo := (10579518383544249943/4000000000000000000)
  directionHi := (2066312184285986317/781250000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree029.table
  base := (-5628639445322505436789391766875992721289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-493758548905844722007134807357340142000000000000)
      constant := (3356901273860695375182271603774117849549425709399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree029.table
  base := (-1127552671714572720988943297166291234001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-495092757021662699408530559834441642000000000000)
      constant := (3375549489474892621109329768186303479180311514955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10579518383544249943/4000000000000000000)
  centralHi := (2066312184285986317/781250000000000000)
  directionLo := (269169525860362245427/100000000000000000000)
  directionHi := (67292381465090561357/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree030.table
  base := (-5963571477434900603539371199132857311387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-510803287621301420892276130726876822000000000000)
      constant := (3594029007347001022069500109710373738282740480517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree030.table
  base := (-2985771769841949201614378289950343144261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-512183502913526914755788978116981822000000000000)
      constant := (3614026695313396073441902819267593161949822901302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269169525860362245427/100000000000000000000)
  centralHi := (67292381465090561357/25000000000000000000)
  directionLo := (68442761914811081053/25000000000000000000)
  directionHi := (273771047659244324213/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree031.table
  base := (-1564084362047289066944811375910283054627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-527848026336758119777417454096413502000000000000)
      constant := (3840412931893169331129021762913903346281495805428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree031.table
  base := (-3131649426189658222496221605236062222413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-529274248805391130103047396399522002000000000000)
      constant := (3861801789282518579211861433031368189417815830566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68442761914811081053/25000000000000000000)
  centralHi := (273771047659244324213/100000000000000000000)
  directionLo := (34787061940510888277/12500000000000000000)
  directionHi := (278296495524087106217/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree032.table
  base := (-6509346302146323876842362883086573519723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-544892765052214818662558777465950182000000000000)
      constant := (4095998627010941088064665868137698933836776029493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree032.table
  base := (-651542179594389585970145470267122234317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-546364994697255345450305814682062182000000000000)
      constant := (4118820722409385222133443305243614556004445441470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34787061940510888277/12500000000000000000)
  centralHi := (278296495524087106217/100000000000000000000)
  directionLo := (141374761101068038477/50000000000000000000)
  directionHi := (56549904440427215391/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree033.table
  base := (-6724622435889340125740107341440973895681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-561937503767671517547700100835486862000000000000)
      constant := (4360740359538891600752999994245577696753905467871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree033.table
  base := (-3364961025160542033333912269589675664393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-563455740589119560797564232964602362000000000000)
      constant := (4385038093996306462065943513688776057517233514926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141374761101068038477/50000000000000000000)
  centralHi := (56549904440427215391/20000000000000000000)
  directionLo := (287133497157827703509/100000000000000000000)
  directionHi := (28713349715782770351/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree034.table
  base := (-1380773650898914367872435514346785106233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-578982242483128216432841424205023542000000000000)
      constant := (4634599670428619020565639534056019880720121704515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree034.table
  base := (-6908488893934052049674517495417390951641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-580546486480983776144822651247142542000000000000)
      constant := (4660415741539220937506182247078636625254959604231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287133497157827703509/100000000000000000000)
  centralHi := (28713349715782770351/10000000000000000000)
  directionLo := (72862884102020804453/25000000000000000000)
  directionHi := (291451536408083217813/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree035.table
  base := (-7048516334353849251611674679242787181591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-12163815942828263577918015256623678000000000000)
      constant := (100358044823142088227796069905546831155012103769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree035.table
  base := (-7052543228112569465448729421321257804443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-12196678211690775336573083051626178000000000000)
      constant := (100916766641702034901451194151480230980581794837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72862884102020804453/25000000000000000000)
  centralHi := (291451536408083217813/100000000000000000000)
  directionLo := (295706528435170441763/100000000000000000000)
  directionHi := (73926632108792610441/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree036.table
  base := (-71597729613640496871654254539955204617/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-613071719914041614203124070944096902000000000000)
      constant := (5209546686039368579828433552087939443290051144700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree036.table
  base := (-7163280980626431743537268483655100081761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-614727978264712206839339487812222902000000000000)
      constant := (5238528548493831981583671503503817763157036513151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295706528435170441763/100000000000000000000)
  centralHi := (73926632108792610441/25000000000000000000)
  directionLo := (299901156789580044137/100000000000000000000)
  directionHi := (149950578394790022069/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree037.table
  base := (-3619327251611483563915399265564094902729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-630116458629498313088265394313633582000000000000)
      constant := (5510584178773029617441761813101777482951190072878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree037.table
  base := (-1448341869895329845215782384158357979347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-631818724156576422186597906094763082000000000000)
      constant := (5541213937071412145095521021481419261316750544385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299901156789580044137/100000000000000000000)
  centralHi := (149950578394790022069/50000000000000000000)
  directionLo := (304037919885458169437/100000000000000000000)
  directionHi := (152018959942729084719/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree038.table
  base := (-7286017821192648058690488137716688039901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-647161197344955011973406717683170262000000000000)
      constant := (5820637317174462792499070697385189307040404149891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree038.table
  base := (-728867709385473122111328311617789801329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-648909470048440637533856324377303262000000000000)
      constant := (5852958556849605981205150163143283881380683490390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304037919885458169437/100000000000000000000)
  centralHi := (152018959942729084719/50000000000000000000)
  directionLo := (61623829680676058337/20000000000000000000)
  directionHi := (154059574201690145843/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree039.table
  base := (-7302585718930590514545093477950065410231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-664205936060411710858548041052706942000000000000)
      constant := (6139689772379736333978697555110947243766882786921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree039.table
  base := (-730489987075231075716783706156064239427/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-666000215940304852881114742659843442000000000000)
      constant := (6173746240414874595240397936023755296625264881570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61623829680676058337/20000000000000000000)
  centralHi := (154059574201690145843/50000000000000000000)
  directionLo := (312147020644715260949/100000000000000000000)
  directionHi := (6242940412894305219/2000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree040.table
  base := (-182224206378437313867443451946118228749/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-681250674775868409743689364422243622000000000000)
      constant := (6467727762547252243716642988974702903170691290360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree040.table
  base := (-1822745361088248295836113844349894294313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-683090961832169068228373160942383622000000000000)
      constant := (6503563348125112281107255590518097135392505472732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312147020644715260949/100000000000000000000)
  centralHi := (6242940412894305219/2000000000000000000)
  directionLo := (316123576124781150267/100000000000000000000)
  directionHi := (79030894031195287567/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree041.table
  base := (-3622840302984617636930131292965614965953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-698295413491325108628830687791780302000000000000)
      constant := (6804739649327836426499341954478936778227242166846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree041.table
  base := (-1811857863544104834253918535552156944489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-700181707724033283575631579224923802000000000000)
      constant := (6842398366709344076971872627723776601990546002396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316123576124781150267/100000000000000000000)
  centralHi := (79030894031195287567/25000000000000000000)
  directionLo := (20003170477849051161/6250000000000000000)
  directionHi := (320050727645584818577/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree042.table
  base := (-7173158046931666294084385486958090938147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-14598778616464934847223918595128918000000000000)
      constant := (145932971416502424472334601650392420795785768973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree042.table
  base := (-1793670077865823078471769700039731628411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-14638213339099948957609999949131918000000000000)
      constant := (146739623933537909347608904194311319361223056596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20003170477849051161/6250000000000000000)
  centralHi := (320050727645584818577/100000000000000000000)
  directionLo := (161965136025485680787/50000000000000000000)
  directionHi := (12957210882038854463/4000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree043.table
  base := (-1767942131975093689572853990769869838791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-732384890922238506399113334530853662000000000000)
      constant := (7505647300430648378443765986119750995172175879524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree043.table
  base := (-7073091697045374905933983004914140642633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-734363199507761714270148415790004162000000000000)
      constant := (7547084750310209243570767185382792485515012113303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161965136025485680787/50000000000000000000)
  centralHi := (12957210882038854463/4000000000000000000)
  directionLo := (163881949917893890683/50000000000000000000)
  directionHi := (327763899835787781367/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree044.table
  base := (-1388364647079255702664269538148697629677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-749429629637695205284254657900390342000000000000)
      constant := (7869527722376430430631230551525921950548441129535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree044.table
  base := (-3471486527163949274956013297647640766883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-751453945399625929617406834072544342000000000000)
      constant := (7912920953953164559550835676908826095213158490106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163881949917893890683/50000000000000000000)
  centralHi := (327763899835787781367/100000000000000000000)
  directionLo := (165776601877430468991/50000000000000000000)
  directionHi := (331553203754860937983/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree045.table
  base := (-6783585470375690596521751737922238935309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-766474368353151904169395981269927022000000000000)
      constant := (8242350917011691179273252862963043673912283963219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree045.table
  base := (-1356916881016241529834709037340009988499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-768544691291490144964665252355084522000000000000)
      constant := (8287744309518069459623809536040885481448645972545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165776601877430468991/50000000000000000000)
  centralHi := (331553203754860937983/100000000000000000000)
  directionLo := (335299686556161786039/100000000000000000000)
  directionHi := (8382492163904044651/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree046.table
  base := (-1319455623033430839369754169138746609211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-783519107068608603054537304639463702000000000000)
      constant := (8624111849199740564231235999162138367512974080505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree046.table
  base := (-6598145761087498734133354540423861812271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-785635437183354360311923670637624702000000000000)
      constant := (8671549846716772235931318886182204050984229528561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335299686556161786039/100000000000000000000)
  centralHi := (8382492163904044651/2500000000000000000)
  directionLo := (339004767944653469191/100000000000000000000)
  directionHi := (42375595993081683649/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree047.table
  base := (-1595772479461080561628393906181702483699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-800563845784065301939678628009000382000000000000)
      constant := (9014806254931147959450721014957050783221734150836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree047.table
  base := (-6383843359344898047239346228576529399/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-802726183075218575659182088920164882000000000000)
      constant := (9064333358267572085547087226796224886158426409000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339004767944653469191/100000000000000000000)
  centralHi := (42375595993081683649/12500000000000000000)
  directionLo := (85667447717086635777/25000000000000000000)
  directionHi := (342669790868346543109/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree048.table
  base := (-1228236156930542659712347328131844799523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-817608584499522000824819951378537062000000000000)
      constant := (9414430521762481699090188448289323320736863556465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree048.table
  base := (-6141834910875545836602099002627327339221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-819816928967082791006440507202705062000000000000)
      constant := (9466091281319348438926786240313296840433712336011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85667447717086635777/25000000000000000000)
  centralHi := (342669790868346543109/100000000000000000000)
  directionLo := (173148013602744201013/50000000000000000000)
  directionHi := (346296027205488402027/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree049.table
  base := (-5871686239782623992627707558857038401207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7286034467802607061809316834840000000000000)
      linear := (-347627373267379716663873917012942000000000000)
      constant := (4091204326557908818846724947811157125683043337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree049.table
  base := (-2936127010942756828431346499636690126377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7286034467802607061809316834840000000000000)
      linear := (-348566295234880052625447282584442000000000000)
      constant := (4113627904028778624625104245562504765201837614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173148013602744201013/50000000000000000000)
  centralHi := (346296027205488402027/100000000000000000000)
  directionLo := (4373558536514708977/1250000000000000000)
  directionHi := (349884682921176718161/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree050.table
  base := (-8710501852670591179543955740938711769/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-851698061930435398595102598117610422000000000000)
      constant := (10240456858077470435181190864728410062145993650560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree050.table
  base := (-34845086999915386143785841033749241067/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-853998420750811221700957343767785422000000000000)
      constant := (10296518749102825136164234669799115729609957343520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4373558536514708977/1250000000000000000)
  centralHi := (349884682921176718161/100000000000000000000)
  directionLo := (353436902752670096193/100000000000000000000)
  directionHi := (176718451376335048097/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree051.table
  base := (-2625191537801783876690494369285661819209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-868742800645892097480243921487147102000000000000)
      constant := (10666854130232808319746088391014229817542586216238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree051.table
  base := (-1312702649127257005220341021197891294627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-871089166642675437048215762050325602000000000000)
      constant := (10725183567367517053597163594862577624928239165428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353436902752670096193/100000000000000000000)
  centralHi := (176718451376335048097/50000000000000000000)
  directionLo := (178476887237499456979/50000000000000000000)
  directionHi := (356953774474998913959/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree052.table
  base := (-4898754591214453784352983264437978495883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-885787539361348796365385244856683782000000000000)
      constant := (11102171536667424577885560050150513051857700684053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree052.table
  base := (-979825091574263246443580275071539022801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-888179912534539652395474180332865782000000000000)
      constant := (11162813213314049187920422840224693285460257018955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178476887237499456979/50000000000000000000)
  centralHi := (356953774474998913959/100000000000000000000)
  directionLo := (90109083197983013383/25000000000000000000)
  directionHi := (360436332791932053533/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree053.table
  base := (-4519905904512003099941840791172554870947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-902832278076805495250526568226220462000000000000)
      constant := (11546407492125709627030114435417781243357442484477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree053.table
  base := (-4520227563897725128952526983850698999977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-905270658426403867742732598615405962000000000000)
      constant := (11609406126811307009413051152719153630235228593207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90109083197983013383/25000000000000000000)
  centralHi := (360436332791932053533/100000000000000000000)
  directionLo := (363885562891748154247/100000000000000000000)
  directionHi := (45485695361468519281/12500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree054.table
  base := (-205694829438606566288587184962836885347/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-919877016792262194135667891595757142000000000000)
      constant := (11999560650787251097798035012040931223151879097540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree054.table
  base := (-2057087759202857767827507589915808325027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-922361404318268083089991016897946142000000000000)
      constant := (12064960983939922826230045340694336782774080235514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363885562891748154247/100000000000000000000)
  centralHi := (45485695361468519281/12500000000000000000)
  directionLo := (5739100057850671783/1562500000000000000)
  directionHi := (367302403702442994113/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree055.table
  base := (-1840388617117893267982446368140052209011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-936921755507718893020809214965293822000000000000)
      constant := (12461629869767460420078294475831360119571525235802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree055.table
  base := (-460127383358851370544701996588275085979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-939452150210132298437249435180486322000000000000)
      constant := (12529476660899411377431373235897507300905381097512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5739100057850671783/1562500000000000000)
  centralHi := (367302403702442994113/100000000000000000000)
  directionLo := (370687750876853788279/100000000000000000000)
  directionHi := (9267193771921344707/2500000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree056.table
  base := (-644118162932025445163591575605740677511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-19468703963738277385835725272139398000000000000)
      constant := (263930901596853119642637128524409296561498255245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree056.table
  base := (-3220800447195374465977110664348232327303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-19521283593918296199683833744143398000000000000)
      constant := (265366371499855923228826660687489854619587897577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370687750876853788279/100000000000000000000)
  centralHi := (9267193771921344707/2500000000000000000)
  directionLo := (374042459534594045603/100000000000000000000)
  directionHi := (93510614883648511401/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree057.table
  base := (-2733373843697321336683542908566246231287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-971011232938632290791091861704367182000000000000)
      constant := (13412512751342033676198201333375800093292779301417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree057.table
  base := (-2733555532256360293337339615848434170339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-973633641993860729131766271745566682000000000000)
      constant := (13485386801316023279155313101050859745021964117949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374042459534594045603/100000000000000000000)
  centralHi := (93510614883648511401/25000000000000000000)
  directionLo := (94341836696145983909/25000000000000000000)
  directionHi := (377367346784583935637/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree058.table
  base := (-44383147077071107284214887941122957501/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-988055971654088989676233185073903862000000000000)
      constant := (13901324888000526309526353381434753975849414574550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree058.table
  base := (-554828699188090935197806467405906976037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-990724387885724944479024690028106862000000000000)
      constant := (13976779765914470261677708884361532106404741394668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94341836696145983909/25000000000000000000)
  centralHi := (377367346784583935637/100000000000000000000)
  directionLo := (190331597024629911551/50000000000000000000)
  directionHi := (380663194049259823103/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree059.table
  base := (-838983862798686739879883040829576406221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1005100710369545688561374508443440542000000000000)
      constant := (14399049992259878456881579536982294156881747466022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree059.table
  base := (-1678104135712578684182376305474451522137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1007815133777589159826283108310647042000000000000)
      constant := (14477130512293443611667765918004981829393339333767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190331597024629911551/50000000000000000000)
  centralHi := (380663194049259823103/100000000000000000000)
  directionLo := (191965374604596627221/50000000000000000000)
  directionHi := (383930749209193254443/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree060.table
  base := (-221965477967571334303521879196832639587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1022145449085002387446515831812977222000000000000)
      constant := (14905687557383221191478018356948749025337981633585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree060.table
  base := (-277486389426247601242506047169711383217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1024905879669453375173541526593187222000000000000)
      constant := (14986438543257185896520171130152215572457369216188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191965374604596627221/50000000000000000000)
  centralHi := (383930749209193254443/100000000000000000000)
  directionLo := (9679268214619857509/2500000000000000000)
  directionHi := (387170728584794300361/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree061.table
  base := (-514755423342324489816998144181812867149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1039190187800459086331657155182513902000000000000)
      constant := (15421237152407132306448227324880037374881921136659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree061.table
  base := (-257428886075663326184741162834196666839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1041996625561317590520799944875727402000000000000)
      constant := (15504703436140982479856851646255322177183340298898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9679268214619857509/2500000000000000000)
  centralHi := (387170728584794300361/100000000000000000000)
  directionLo := (390383818769974714119/100000000000000000000)
  directionHi := (9759595469249367853/2500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree062.table
  base := (107231946403910708883165223457704845847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1056234926515915785216798478552050582000000000000)
      constant := (15945698410736345062979632167391531395291873189623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree062.table
  base := (107143312891997717971019564251008159811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1059087371453181805868058363158267582000000000000)
      constant := (16031924831565787721166124607891394652597363739299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390383818769974714119/100000000000000000000)
  centralHi := (9759595469249367853/2500000000000000000)
  directionLo := (393570678331067327859/100000000000000000000)
  directionHi := (19678533916553366393/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree063.table
  base := (756120912971752870484315690678536632829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-21903666637374948655141628610644638000000000000)
      constant := (336307571846320316209229137047222652207736114989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree063.table
  base := (756044168689384925183616402891566294949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-21962818721327469820720750641649138000000000000)
      constant := (338124539263343142293061715250373609616189581909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393570678331067327859/100000000000000000000)
  centralHi := (19678533916553366393/5000000000000000000)
  directionLo := (198365969691454686431/50000000000000000000)
  directionHi := (396731939382909372863/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree064.table
  base := (715949863820860188164764767484414332431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1090324403946829182987081125291123942000000000000)
      constant := (17021354716191756052543600836919594271087355425758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree064.table
  base := (715916643937311693436962268178441682931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1093268863236910236562575199723347942000000000000)
      constant := (17113235953192047581284774201711432427330138734758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198365969691454686431/50000000000000000000)
  centralHi := (396731939382909372863/100000000000000000000)
  directionLo := (399868209052773392183/100000000000000000000)
  directionHi := (49983526131596674023/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree065.table
  base := (2134558391007786484472462177562513278131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1107369142662285881872222448660660622000000000000)
      constant := (17572549272005855193072200984312578890528876924179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree065.table
  base := (2134500880761797736856709857001344422589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1110359609128774451909833618005888122000000000000)
      constant := (17667325198271605926729646151827842264862807902301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399868209052773392183/100000000000000000000)
  centralHi := (49983526131596674023/12500000000000000000)
  directionLo := (201490035420874158551/50000000000000000000)
  directionHi := (402980070841748317103/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree066.table
  base := (2864088391141012777173064988168930561647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1124413881377742580757363772030197302000000000000)
      constant := (18132654495618929660682416959225529845838542431823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree066.table
  base := (143201930880702782194388248393724971327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1127450355020638667257092036288428302000000000000)
      constant := (18230369970965328810047831027115162194415459978860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201490035420874158551/50000000000000000000)
  centralHi := (402980070841748317103/100000000000000000000)
  directionLo := (25379255368263529931/6250000000000000000)
  directionHi := (406068085892216478897/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree067.table
  base := (5792771969949883935215834761349910647/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1141458620093199279642505095399733982000000000000)
      constant := (18701670223317942125900682328291301336234733014375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree067.table
  base := (3620439409851601589634193526348013488467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1144541100912502882604350454570968482000000000000)
      constant := (18802370111135046273466510701301008418850079393203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25379255368263529931/6250000000000000000)
  centralHi := (406068085892216478897/100000000000000000000)
  directionLo := (409132794169223872239/100000000000000000000)
  directionHi := (5114159927115298403/1250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree068.table
  base := (880746898123567976166137909848350501593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1158503358808655978527646418769270662000000000000)
      constant := (19279596315702294200881645852835656730083209886685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree068.table
  base := (4403697224264250978379448731504544295207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1161631846804367097951608872853508662000000000000)
      constant := (19383325482484452737892191304156936049713919993863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409132794169223872239/100000000000000000000)
  centralHi := (5114159927115298403/1250000000000000000)
  directionLo := (82434943112557435651/20000000000000000000)
  directionHi := (25760919722674198641/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree069.table
  base := (5213839164394755044480364170920863750193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1175548097524112677412787742138807342000000000000)
      constant := (19866432654057504447912167666780274754268383814737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree069.table
  base := (5213806925208165196856433226209253786133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1178722592696231313298867291136048842000000000000)
      constant := (19973235968994172024418008319884035746165814678197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82434943112557435651/20000000000000000000)
  centralHi := (25760919722674198641/6250000000000000000)
  directionLo := (415194350917510102983/100000000000000000000)
  directionHi := (51899293864688762873/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree070.table
  base := (6050792026850356199729309705451450398539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-24338629311011619924447531949149878000000000000)
      constant := (417595492597408468749692130082569752143192819099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree070.table
  base := (756345517567247496315991299090436872301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-24404353848736643441757667539154878000000000000)
      constant := (419838805548837323661420673817061717848340202728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415194350917510102983/100000000000000000000)
  centralHi := (51899293864688762873/12500000000000000000)
  directionLo := (418192182995283318181/100000000000000000000)
  directionHi := (209096091497641659091/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree071.table
  base := (6914589265539881131735657150105256121931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1209637574955026075183070388877880702000000000000)
      constant := (21066835679221851828151533378415130968997848318379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree071.table
  base := (6914565147677048875732688050027727195973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1212904084479959743993384127701129202000000000000)
      constant := (21179921907084260720320256234640219262333770806757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418192182995283318181/100000000000000000000)
  centralHi := (209096091497641659091/50000000000000000000)
  directionLo := (26323042336019244323/6250000000000000000)
  directionHi := (421168677376307909169/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree072.table
  base := (3902613816320346529543594002697528904321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1226682313670482774068211712247417382000000000000)
      constant := (21680402206532424608229410219056031743510551699778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree072.table
  base := (7805206776778918058599320488174109017447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1229994830371823959340642545983669382000000000000)
      constant := (21796697202957837839519044813280717934380126334023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26323042336019244323/6250000000000000000)
  centralHi := (421168677376307909169/100000000000000000000)
  directionLo := (424124283303204115431/100000000000000000000)
  directionHi := (53015535412900514429/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree073.table
  base := (8722704361062447903219201065783098463951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1243727052385939472953353035616954062000000000000)
      constant := (22302878656693370442076593023952005860447003216559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree073.table
  base := (4361343164199173451565822190583667275659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1247085576263688174687900964266209562000000000000)
      constant := (22422427298530568491242843431474310301354835899862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424124283303204115431/100000000000000000000)
  centralHi := (53015535412900514429/12500000000000000000)
  directionLo := (106764858618134668277/25000000000000000000)
  directionHi := (427059434472538673109/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree074.table
  base := (9667017093081436569772946431732859001187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1260771791101396171838494358986490742000000000000)
      constant := (22934264976441331798029041424893874721291546527683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree074.table
  base := (9667001503483564145242583182157820035553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1264176322155552390035159382548749742000000000000)
      constant := (23057112141864553419398719566167428494843558142977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106764858618134668277/25000000000000000000)
  centralHi := (427059434472538673109/100000000000000000000)
  directionLo := (429974549777719472359/100000000000000000000)
  directionHi := (10749363744442986809/2500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree075.table
  base := (10638163819617493102017907913667174171969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1277816529816852870723635682356027422000000000000)
      constant := (23574561120389160565236762720068254879723519226721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree075.table
  base := (10638150343834238550186659950436115220769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1281267068047416605382417800831289922000000000000)
      constant := (23700751688722071317259557035083212857877429465921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429974549777719472359/100000000000000000000)
  centralHi := (10749363744442986809/2500000000000000000)
  directionLo := (108217508501715125633/25000000000000000000)
  directionHi := (432870034006860502533/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree076.table
  base := (5818071414278411206814305622295064418229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1294861268532309569608777005725564102000000000000)
      constant := (24223767049858478589880422343380173213855582206122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree076.table
  base := (11636131181451300192789244055593312992347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1298357813939280820729676219113830102000000000000)
      constant := (24353345901421340184154106431078420096149928008123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108217508501715125633/25000000000000000000)
  centralHi := (432870034006860502533/100000000000000000000)
  directionLo := (87149255699781756771/20000000000000000000)
  directionHi := (27234142406181798991/6250000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree077.table
  base := (3165238165191368933649062896188268639657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-26773591984648291193753435287655118000000000000)
      constant := (507793525140530157205943111318686213247584411748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree077.table
  base := (12660942595443227685622465082467848126537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-26845888976145817062794584436660618000000000000)
      constant := (510508056078836466783577392790883705168106745017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87149255699781756771/20000000000000000000)
  centralHi := (27234142406181798991/6250000000000000000)
  directionLo := (438603661761044333251/100000000000000000000)
  directionHi := (109650915440261083313/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree078.table
  base := (13712592072642736539405136467896225349009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1328950745963222967379059652464637462000000000000)
      constant := (25548908138377462925434759315628101563925490460081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree078.table
  base := (13712583375355417461099590687013186023507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1332539305723009251424193055678910462000000000000)
      constant := (25685398200701620538696330503442910869575720848563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438603661761044333251/100000000000000000000)
  centralHi := (109650915440261083313/25000000000000000000)
  directionLo := (441442550050110813563/100000000000000000000)
  directionHi := (110360637512527703391/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree079.table
  base := (14791060004237063199949473656484284980127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1345995484678679666264200975834174142000000000000)
      constant := (26224843245387559440426650321027314543344613878143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree079.table
  base := (7395526244980209090947672843492349135839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1349630051614873466771451473961450642000000000000)
      constant := (26364856236640772548848643873577683004517762143102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441442550050110813563/100000000000000000000)
  centralHi := (110360637512527703391/25000000000000000000)
  directionLo := (444263297920605408881/100000000000000000000)
  directionHi := (222131648960302704441/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree080.table
  base := (3179271110418852964697150767696379157013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1363040223394136365149342299203710822000000000000)
      constant := (26909688032506325490521198817253488814017465480585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree080.table
  base := (3974087265172976413674320042363430942949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1366720797506737682118709892243990822000000000000)
      constant := (27053268835832743165904193061362597358812157382164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444263297920605408881/100000000000000000000)
  centralHi := (222131648960302704441/50000000000000000000)
  directionLo := (111766562185387262013/25000000000000000000)
  directionHi := (447066248741549048053/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree081.table
  base := (8514238973066156310939994029639896546483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1380084962109593064034483622573247502000000000000)
      constant := (27603442482336831032627410766627145886281332742694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree081.table
  base := (17028472339028305949847960398552540541837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1383811543398601897465968310526531002000000000000)
      constant := (27750635981367674776523921614353762602353504543533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111766562185387262013/25000000000000000000)
  centralHi := (447066248741549048053/100000000000000000000)
  directionLo := (224925867592185033103/50000000000000000000)
  directionHi := (449851735184370066207/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree082.table
  base := (18187426529943029425215079840350866085083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1397129700825049762919624945942784182000000000000)
      constant := (28306106580050153028626094513348011492885904818747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree082.table
  base := (18187421687236335325199271365418394311373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1400902289290466112813226728809071182000000000000)
      constant := (28456957658838529028089407787052925173653776245357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224925867592185033103/50000000000000000000)
  centralHi := (449851735184370066207/100000000000000000000)
  directionLo := (226310039841881860851/50000000000000000000)
  directionHi := (452620079683763721703/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree083.table
  base := (4843300186002685675441652109939394149403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1414174439540506461804766269312320862000000000000)
      constant := (29017680313006267884712010882915188031734842070508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree083.table
  base := (605412392561664892287491926661141625839/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1417993035182330328160485147091611362000000000000)
      constant := (29172233855970645705628581240717772954427311409632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226310039841881860851/50000000000000000000)
  centralHi := (452620079683763721703/100000000000000000000)
  directionLo := (455371594873334878839/100000000000000000000)
  directionHi := (11384289871833371971/2500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree084.table
  base := (2573225013926784093762051998892386105449/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-29208554658284962463059338626160358000000000000)
      constant := (606901299396551937509374553837271368659538499272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree084.table
  base := (5146449125080492515883760367450787198371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-29287424103554990683831501334166358000000000000)
      constant := (610131929842984879408857853432430275522896656844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455371594873334878839/100000000000000000000)
  centralHi := (11384289871833371971/2500000000000000000)
  directionLo := (458106583997690035471/100000000000000000000)
  directionHi := (28631661499855627217/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree085.table
  base := (2728153028205427727870232908281038784131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1448263916971419859575048916051394222000000000000)
      constant := (30467556643141008652468383090692255468613219825432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree085.table
  base := (21825221107896308642947606207017639854201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1452174526966058758855001983656691722000000000000)
      constant := (30629649768935789086776101958081752735105013478809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458106583997690035471/100000000000000000000)
  centralHi := (28631661499855627217/6250000000000000000)
  directionLo := (23041267065125815453/5000000000000000000)
  directionHi := (460825341302516309061/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree086.table
  base := (23091472740216178211313550621258511972557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1465308655686876558460190239420930902000000000000)
      constant := (31205859223308780783381860372114776817298642940013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree086.table
  base := (5772867512177303658990262327331089735633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1469265272857922974202260401939231902000000000000)
      constant := (31371789468268948597656216712433551333789970894788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23041267065125815453/5000000000000000000)
  centralHi := (460825341302516309061/100000000000000000000)
  directionLo := (231764076202033870783/50000000000000000000)
  directionHi := (463528152404067741567/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree087.table
  base := (12192272679914814948259315019668172478503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1482353394402333257345331562790467582000000000000)
      constant := (31953071404263170587560642145049946771950827159054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree087.table
  base := (3048067879567638873109300880607012825321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1486356018749787189549518820221772082000000000000)
      constant := (32122883653839748582387663090269193716599537111112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231764076202033870783/50000000000000000000)
  centralHi := (463528152404067741567/100000000000000000000)
  directionLo := (116553823659843056969/25000000000000000000)
  directionHi := (466215294639372227877/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree088.table
  base := (25704441832817346899064438593541414153567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1499398133117789956230472886160004262000000000000)
      constant := (32709193180318779480339688025701288525015959479103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree088.table
  base := (3213054978448251224456764009568236654501/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1503446764641651404896777238504312262000000000000)
      constant := (32882932320140365774202437725574893759007695852072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116553823659843056969/25000000000000000000)
  centralHi := (466215294639372227877/100000000000000000000)
  directionLo := (234443518699187260327/50000000000000000000)
  directionHi := (93777407479674904131/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree089.table
  base := (27051161944719800179295892239797728234077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1516442871833246655115614209529540942000000000000)
      constant := (33474224546630750311048388653533324959715587613693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree089.table
  base := (27051160214185582533698898265991802223599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1520537510533515620244035656786852442000000000000)
      constant := (33651935462479589004250406603606618245959545021391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234443518699187260327/50000000000000000000)
  centralHi := (93777407479674904131/20000000000000000000)
  directionLo := (58942955304892653731/12500000000000000000)
  directionHi := (471543642439141229849/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree090.table
  base := (5684941102560627279285717002353227145587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1533487610548703354000755532899077622000000000000)
      constant := (34248165499070940954260403446300834608125001136415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree090.table
  base := (5684940803897966462934311431199692165689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1537628256425379835591294075069392622000000000000)
      constant := (34429893076862198401267535889072990487561548451005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58942955304892653731/12500000000000000000)
  centralHi := (471543642439141229849/100000000000000000000)
  directionLo := (474185364187171725401/100000000000000000000)
  directionHi := (237092682093585862701/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree091.table
  base := (7456268095346520933744903948438739128941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-31643517331921633732365241964665598000000000000)
      constant := (714918694573925599944096160113328911906984350324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree091.table
  base := (29825071092907013475380927321192414519209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-31728959230964164304868418231672098000000000000)
      constant := (718710309385432132319407409908019304982350636569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474185364187171725401/100000000000000000000)
  centralHi := (237092682093585862701/50000000000000000000)
  directionLo := (95362490003956731643/20000000000000000000)
  directionHi := (59601556252472957277/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree092.table
  base := (31252262417855570361367462881770358002897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1567577087979616751771038179638150982000000000000)
      constant := (35822776148789127540739227192241551177576668153073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree092.table
  base := (31252261306225874538159952074677348678691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1571809748209108266285810911634472982000000000000)
      constant := (36012671708655095715367448416249299790096446489219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95362490003956731643/20000000000000000000)
  centralHi := (59601556252472957277/12500000000000000000)
  directionLo := (11985628513411820049/2500000000000000000)
  directionHi := (479425140536472801961/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree093.table
  base := (8176568877317335479467001608331340756099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1584621826695073450656179503007687662000000000000)
      constant := (36623445840519780900020314675487436207012397255564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree093.table
  base := (32706274550310678734116405721833184054463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1588900494100972481633069329917013162000000000000)
      constant := (36817492720703475684849316690644858563473030123167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11985628513411820049/2500000000000000000)
  centralHi := (479425140536472801961/100000000000000000000)
  directionLo := (60252958727010439679/12500000000000000000)
  directionHi := (482023669816083517433/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree094.table
  base := (6837422311891786577103197107645259108243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1601666565410530149541320826377224342000000000000)
      constant := (37433025107141771805048840415381238244608247935935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree094.table
  base := (3418711073228424028712793274733258688923/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1605991239992836696980327748199553342000000000000)
      constant := (37631268193933125052333515790131662829407876933070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60252958727010439679/12500000000000000000)
  centralHi := (482023669816083517433/100000000000000000000)
  directionLo := (242304132830783920063/50000000000000000000)
  directionHi := (484608265661567840127/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree095.table
  base := (35694770486559173469547858701558226782273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1618711304125986848426462149746761022000000000000)
      constant := (38251513946805683468204773093139460680262370383457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree095.table
  base := (4461846221640849257197006167251186851901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1623081985884700912327586166482093522000000000000)
      constant := (38453998126558907592373038290320123754455817264872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242304132830783920063/50000000000000000000)
  centralHi := (484608265661567840127/100000000000000000000)
  directionLo := (60897393729132191329/12500000000000000000)
  directionHi := (487179149833057530633/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree096.table
  base := (37229252220901334144728738646119127723759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1635756042841443547311603473116297702000000000000)
      constant := (39078912357937628993764965643168846981479589082831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree096.table
  base := (37229251605629221414083687801500996248127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1640172731776565127674844584764633702000000000000)
      constant := (39285682517062501501084377172578461571750403290143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60897393729132191329/12500000000000000000)
  centralHi := (487179149833057530633/100000000000000000000)
  directionLo := (489736538269923992149/100000000000000000000)
  directionHi := (9794730765398479843/2000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree097.table
  base := (19395278351608154459168766119420060640007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (331338)
      previous := (165669)
      next := (165669)
      square := (1859259087808912695866103700760000000000000)
      linear := (-175661683659995774917286087414798000000000000)
      constant := (4242238318545930436265905188225146131193313614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree097.table
  base := (38790556172648266968488419944332016564493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (331338)
      previous := (165669)
      next := (165669)
      square := (1859259087808912695866103700760000000000000)
      linear := (-176135984447702130196843766930298000000000000)
      constant := (4264674393044211178839861465418857171771347693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489736538269923992149/100000000000000000000)
  centralHi := (9794730765398479843/2000000000000000000)
  directionLo := (492280641302455376699/100000000000000000000)
  directionHi := (4922806413024553767/1000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree098.table
  base := (10094670970775539420191033345775916911483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7286034467802607061809316834840000000000000)
      linear := (-695479183786904183707574393942262000000000000)
      constant := (16976442269658535705436867562825688408880574188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree098.table
  base := (40378683425619137407519134335669058073393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7286034467802607061809316834840000000000000)
      linear := (-697357027721904855630721125085262000000000000)
      constant := (17066186866611088859395847088375201167412554737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492280641302455376699/100000000000000000000)
  centralHi := (4922806413024553767/1000000000000000000)
  directionLo := (49481166385373813467/10000000000000000000)
  directionHi := (494811663853738134671/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree099.table
  base := (41993633717717073344660845389616515175319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1686890258987813643967027443224907742000000000000)
      constant := (41614565007724243606062481348133986693874268106871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree099.table
  base := (10498408330821869387872721689099318350103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1691444969452157773716619839612254242000000000000)
      constant := (41834462423871248101046434973748432703964168095708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49481166385373813467/10000000000000000000)
  centralHi := (494811663853738134671/100000000000000000000)
  directionLo := (248664902816145703487/50000000000000000000)
  directionHi := (19893192225291656279/4000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree100.table
  base := (43635406170664585619991706803608420309261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1703934997703270342852168766594444422000000000000)
      constant := (42477601693198724618861153889830558755682298034349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree100.table
  base := (872708116612566840128815341592535487069/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1708535715344021989063878257894794422000000000000)
      constant := (42701964634775805373995750223461990626059758131050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248664902816145703487/50000000000000000000)
  centralHi := (19893192225291656279/4000000000000000000)
  directionLo := (499835261315966740229/100000000000000000000)
  directionHi := (49983526131596674023/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree101.table
  base := (9060800242208541771540069954325829378089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1720979736418727041737310089963981102000000000000)
      constant := (43349547945175480231234233395749589089064365009005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree101.table
  base := (45304000917924569572000694397889598009113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1725626461235886204411136676177334602000000000000)
      constant := (43578421298775555514125408489236194851630253865017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499835261315966740229/100000000000000000000)
  centralHi := (49983526131596674023/10000000000000000000)
  directionLo := (15697756897737261689/3125000000000000000)
  directionHi := (502328220727592374049/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree102.table
  base := (58749273515791141020997432651188574319/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1738024475134183740622451413333517782000000000000)
      constant := (44230403763062207390540769079741529608510158296800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree102.table
  base := (23499709279990523112966149041809038330697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1742717207127750419758395094459874782000000000000)
      constant := (44463832415301315473802996540078328551420241806546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15697756897737261689/3125000000000000000)
  centralHi := (502328220727592374049/100000000000000000000)
  directionLo := (252404434501405289981/50000000000000000000)
  directionHi := (504808869002810579963/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree103.table
  base := (48721658953208349986906002045815428163039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1755069213849640439507592736703054462000000000000)
      constant := (45120169146356779184632172794834054150970067516351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree103.table
  base := (12180414683863704180156280584232644383953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1759807953019614635105653512742414962000000000000)
      constant := (45358197983870926358943149340519163560486726714308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252404434501405289981/50000000000000000000)
  centralHi := (504808869002810579963/100000000000000000000)
  directionLo := (253638693375264009597/50000000000000000000)
  directionHi := (101455477350105603839/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree104.table
  base := (25235360806971901354078455446007738415731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1772113952565097138392734060072591142000000000000)
      constant := (46018844094633914951927416500293503993238849525158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree104.table
  base := (50470721426283964484108130803906797888579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1776898698911478850452911931024955142000000000000)
      constant := (46261518004076351249711220060547959134262069186211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253638693375264009597/50000000000000000000)
  centralHi := (101455477350105603839/20000000000000000000)
  directionLo := (509733950206372645461/100000000000000000000)
  directionHi := (254866975103186322731/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree105.table
  base := (52246606778912395617460847618086781799847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-36513442679194976270977048641676078000000000000)
      constant := (957682216480281847097082850832647662967783260727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree105.table
  base := (10449321323440140215536832701695514398609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-36612029485782511546942252026683578000000000000)
      constant := (962730458685156640817928677772875448269245459845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509733950206372645461/100000000000000000000)
  centralHi := (254866975103186322731/50000000000000000000)
  directionLo := (256089365689763070207/50000000000000000000)
  directionHi := (102435746275905228083/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree106.table
  base := (27024657217328160084974006816054792416427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1806203429996010536163016706811664502000000000000)
      constant := (47842922684752440378163671842534502041945268209686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree106.table
  base := (54049314295316254973492770065206487939177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1811080190695207281147428767590035502000000000000)
      constant := (48095021398068728456460165606086529602892339059593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256089365689763070207/50000000000000000000)
  centralHi := (102435746275905228083/20000000000000000000)
  directionLo := (51461189819327807947/10000000000000000000)
  directionHi := (514611898193278079471/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree107.table
  base := (27939422284910347269127971517336938578703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1823248168711467235048158030181201182000000000000)
      constant := (48768326326033286325591371042102039059927853362654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree107.table
  base := (6984855556220872528691443479663176647237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1828170936587071496494687185872575682000000000000)
      constant := (49025204771319089695607611490205552613850567137064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51461189819327807947/10000000000000000000)
  centralHi := (514611898193278079471/100000000000000000000)
  directionLo := (517033614619626844863/100000000000000000000)
  directionHi := (8078650228431669451/1562500000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree108.table
  base := (2886759858742064105047840446811583363183/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1840292907426923933933299353550737862000000000000)
      constant := (49702639531160282594447351659390125857238348432940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree108.table
  base := (11547039414282533172763943333784262702827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1845261682478935711841945604155115862000000000000)
      constant := (49964342595117272528965016220900068699889645412215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517033614619626844863/100000000000000000000)
  centralHi := (8078650228431669451/1562500000000000000)
  directionLo := (519444040808232603039/100000000000000000000)
  directionHi := (3246525255051453769/625000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree109.table
  base := (59618372241678155886465034804380058567987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1857337646142380632818440676920274542000000000000)
      constant := (50645862299951799122157181190685059805529921428883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree109.table
  base := (2980918607628967823001201238293142451259/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1862352428370799927189204022437656042000000000000)
      constant := (50912434869289914560656396559888235153093482606620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519444040808232603039/100000000000000000000)
  centralHi := (3246525255051453769/625000000000000000)
  directionLo := (65230416651251166117/12500000000000000000)
  directionHi := (521843333210009328937/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree110.table
  base := (61528369763588559566311259525349240251827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1874382384857837331703582000289811222000000000000)
      constant := (51597994632255510239819601342841417084672186023443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree110.table
  base := (61528369686840127908412767617685158656639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1879443174262664142536462440720196222000000000000)
      constant := (51869481593691825090276486582989251523378559558751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65230416651251166117/12500000000000000000)
  centralHi := (521843333210009328937/100000000000000000000)
  directionLo := (524231644695625783779/100000000000000000000)
  directionHi := (26211582234781289189/5000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree111.table
  base := (6346518973493320755606854924137870363983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1891427123573294030588723323659347902000000000000)
      constant := (52559036527944018796043252993236125323335732288470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree111.table
  base := (63465189668828228261288235172497676491719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1896533920154528357883720859002736402000000000000)
      constant := (52835482768201763776274079793141467569103512354471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524231644695625783779/100000000000000000000)
  centralHi := (26211582234781289189/5000000000000000000)
  directionLo := (131652281167292359733/25000000000000000000)
  directionHi := (526609124669169438933/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree112.table
  base := (13085766430202222550893286283072439787989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-38948405352831647540282951980181318000000000000)
      constant := (1092428326263492341814580632354064579561471182745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree112.table
  base := (65428832094077817209047590719218474603577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-39053564613191685167979168924189318000000000000)
      constant := (1098172212096302913878007667750597980749707743657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131652281167292359733/25000000000000000000)
  centralHi := (526609124669169438933/100000000000000000000)
  directionLo := (10579518383544249943/2000000000000000000)
  directionHi := (528975919177212497151/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree113.table
  base := (67419297007918751962316394005373051106961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1925516601004207428359005970398421262000000000000)
      constant := (54507849009068643570708618850944760416914815913649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree113.table
  base := (16854824239722059934516956940978102759099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1930715411938256788578237695567816762000000000000)
      constant := (54794348467159460570802721900591204748934921363564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10579518383544249943/2000000000000000000)
  centralHi := (528975919177212497151/100000000000000000000)
  directionLo := (3320826068834408207/625000000000000000)
  directionHi := (531332171013505313121/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree114.table
  base := (1388731686048599888388998032280749819239/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1942561339719664127244147293767957942000000000000)
      constant := (55495619594343693712387612365344023982658831107550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree114.table
  base := (69436584260208368066209272597593576739293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1947806157830121003925496113850356942000000000000)
      constant := (55787212991454689093428650927560414593459558816637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3320826068834408207/625000000000000000)
  centralHi := (531332171013505313121/100000000000000000000)
  directionLo := (533678019819509582969/100000000000000000000)
  directionHi := (53367801981950958297/10000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree115.table
  base := (71480694031893743814944874724389802347513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1959606078435120826129288617137494622000000000000)
      constant := (56492299742676384233331524031880466949340887310617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree115.table
  base := (71480693995538056257547089204582253470751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1964896903721985219272754532132897122000000000000)
      constant := (56789031965548047528560371406933185934398017077759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533678019819509582969/100000000000000000000)
  centralHi := (53367801981950958297/10000000000000000000)
  directionLo := (536013602180971589217/100000000000000000000)
  directionHi := (268006801090485794609/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree116.table
  base := (2942065047765867675561688039878873301479/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1976650817150577525014429940507031302000000000000)
      constant := (57497889454017843817174361405861379133589295057775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree116.table
  base := (9193953270355523377781484538707301308679/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1981987649613849434620012950415437302000000000000)
      constant := (57799805389393605705205291726036411579840632536888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536013602180971589217/100000000000000000000)
  centralHi := (268006801090485794609/50000000000000000000)
  directionLo := (269169525860362245427/50000000000000000000)
  directionHi := (107667810344144898171/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree117.table
  base := (75649380787438963712692817367703615708953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1993695555866034223899571263876567982000000000000)
      constant := (58512388728328541023645102742164562450813498603577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree117.table
  base := (75649380760489161209648805761484664126709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-1999078395505713649967271368697977482000000000000)
      constant := (58819533262954368606212124486029775334648460159381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269169525860362245427/50000000000000000000)
  centralHi := (107667810344144898171/20000000000000000000)
  directionLo := (540654499187898080299/100000000000000000000)
  directionHi := (5406544991878980803/1000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree118.table
  base := (38886978905185380292560271822296742886041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2010740294581490922784712587246104662000000000000)
      constant := (59535797565576852987696325047087111444418476410738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree118.table
  base := (38886978893584998429961060437659018836467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2016169141397577865314529786980517662000000000000)
      constant := (59848215586200900554399834289306438447931591050406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540654499187898080299/100000000000000000000)
  centralHi := (5406544991878980803/1000000000000000000)
  directionLo := (542960072543704537123/100000000000000000000)
  directionHi := (135740018135926134281/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree119.table
  base := (9990669657729798060719988248889415285441/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-41383368026468318809588855318686558000000000000)
      constant := (1236083999300772368518615337063240816300920032648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree119.table
  base := (79925357241866474452015163868217503541283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-41495099740600858789016085821695058000000000000)
      constant := (1242568415492043954314005193681266533050176655603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542960072543704537123/100000000000000000000)
  centralHi := (135740018135926134281/25000000000000000000)
  directionLo := (21810235881758377759/4000000000000000000)
  directionHi := (68156987130494930497/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree120.table
  base := (8210357914098826519234547769593178760219/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2044829772012404320554995233985178022000000000000)
      constant := (61609343928792237220219251893974965917107162709710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree120.table
  base := (16420715824759399008078227275691398922293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2050350633181306296009046623545598022000000000000)
      constant := (61932443581664471118358372767635701511380557318185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21810235881758377759/4000000000000000000)
  centralHi := (68156987130494930497/12500000000000000000)
  directionLo := (21901683812739545937/4000000000000000000)
  directionHi := (273771047659244324213/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree121.table
  base := (42154311723588906766405023173840109425317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2061874510727861019440136557354714702000000000000)
      constant := (62659481454725509738348153236525603580176642349706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree121.table
  base := (84308623432381014165363979402080132017159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2067441379073170511356305041828138202000000000000)
      constant := (62987989253850737540202521224934453033120827123431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21901683812739545937/4000000000000000000)
  centralHi := (273771047659244324213/50000000000000000000)
  directionLo := (137454696861890853563/25000000000000000000)
  directionHi := (549818787447563414253/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree122.table
  base := (21635122544985524223067144823750089806973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2078919249443317718325277880724251382000000000000)
      constant := (63718528543527160314911594237158539564320541223028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree122.table
  base := (86540490167207081740303793503240451606463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2084532124965034726703563460110678382000000000000)
      constant := (64052489375659657954308593024454012290405670091167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137454696861890853563/25000000000000000000)
  centralHi := (549818787447563414253/100000000000000000000)
  directionLo := (27604304551774933451/5000000000000000000)
  directionHi := (552086091035498669021/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree123.table
  base := (88799179338965480411707769786591909703151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2095963988158774417210419204093788062000000000000)
      constant := (64786485195190058439968891551935388052431071569359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree123.table
  base := (4439958966400283040870586446943864762291/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2101622870856898942050821878393218562000000000000)
      constant := (65125943947085143249063031821459248267793976832380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27604304551774933451/5000000000000000000)
  centralHi := (552086091035498669021/100000000000000000000)
  directionLo := (554344121281541986737/100000000000000000000)
  directionHi := (277172060640770993369/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree124.table
  base := (91084690924057503013896494545211402306417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2113008726874231116095560527463324742000000000000)
      constant := (65863351409709901405610167179819832364406887204753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree124.table
  base := (9108469091462601983772635616529803472341/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2118713616748763157398080296675758742000000000000)
      constant := (66208352968123788246460755930475734908118867820690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554344121281541986737/100000000000000000000)
  centralHi := (277172060640770993369/50000000000000000000)
  directionLo := (556592991048174212433/100000000000000000000)
  directionHi := (278296495524087106217/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree125.table
  base := (46698512467566182324423721203939457208147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2130053465589687814980701850832861422000000000000)
      constant := (66949127187084750902133957324443192601488727500646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree125.table
  base := (93397024927016596771643054825616240206393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2135804362640627372745338714958298922000000000000)
      constant := (67299716438774428108226909106579467663048786120537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556592991048174212433/100000000000000000000)
  centralHi := (278296495524087106217/50000000000000000000)
  directionLo := (111766562185387262013/20000000000000000000)
  directionHi := (279416405463468155033/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree126.table
  base := (95736181372191492673486747654776289629317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-43818330700104990078894758657191798000000000000)
      constant := (1388649235251319166836192377503352353346989938997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree126.table
  base := (95736181365208322088877885014815802403439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-43936634868010032410053002719200798000000000000)
      constant := (1395919068551791052752677981445321805355883919999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111766562185387262013/20000000000000000000)
  centralHi := (279416405463468155033/50000000000000000000)
  directionLo := (140265922325472767101/25000000000000000000)
  directionHi := (112212737860378213681/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree127.table
  base := (49051080117654366688805258109824390498869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2164142943020601212750984497571934782000000000000)
      constant := (69147407430401234486325975136797242917358928137642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree127.table
  base := (9810216022930046300847204225730302141649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2169985854424355803439855551523379282000000000000)
      constant := (69509306728916031223062456502662259751547118338410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140265922325472767101/25000000000000000000)
  centralHi := (112212737860378213681/20000000000000000000)
  directionLo := (563285732410822706161/100000000000000000000)
  directionHi := (281642866205411353081/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree128.table
  base := (100494961524617781310908234247863188697053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2181187681736057911636125820941471462000000000000)
      constant := (70259911896347557130966889370557482102623822596477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree128.table
  base := (100494961519448615886040729549044465716293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2187076600316220018787113969805919462000000000000)
      constant := (70627533548412752101440685593522649242396966609637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563285732410822706161/100000000000000000000)
  centralHi := (281642866205411353081/50000000000000000000)
  directionLo := (565499044404272153909/100000000000000000000)
  directionHi := (56549904440427215391/10000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree129.table
  base := (102914585240301515934555714868403863430263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2198232420451514610521267144311008142000000000000)
      constant := (71381325925157738540449507143924186497387842305367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree129.table
  base := (25728646308963632132687191447224026572751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2204167346208084234134372388088459642000000000000)
      constant := (71754714817532481906588481069629362265285027983036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565499044404272153909/100000000000000000000)
  centralHi := (56549904440427215391/10000000000000000000)
  directionLo := (11354074548050016689/2000000000000000000)
  directionHi := (567703727402500834451/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree130.table
  base := (3292532230705717614047293601719992937981/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2215277159166971309406408467680544822000000000000)
      constant := (72511649516836817106205163301733905440139686810528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree130.table
  base := (52680515689378740550799857203632044906503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2221258092099948449481630806370999822000000000000)
      constant := (72890850536280626218731413863470774953342426863054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11354074548050016689/2000000000000000000)
  centralHi := (567703727402500834451/100000000000000000000)
  directionLo := (284949940775235547517/50000000000000000000)
  directionHi := (113979976310094219007/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree131.table
  base := (107834299951717644665553559417930400413831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2232321897882428008291549791050081502000000000000)
      constant := (73650882671390565287592505400010707834122459845479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree131.table
  base := (53917149974213497099807094875166868165033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2238348837991812664828889224653540002000000000000)
      constant := (74035940704663273780192826082927088987436147976594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284949940775235547517/50000000000000000000)
  centralHi := (113979976310094219007/20000000000000000000)
  directionLo := (143021901267731761331/25000000000000000000)
  directionHi := (22883504202837081813/4000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree132.table
  base := (110334390947987099513939350455048103007949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2249366636597884707176691114419618182000000000000)
      constant := (74799025388825343369287163885849175154485502930541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree132.table
  base := (22066878189031333372508399961018353439439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2255439583883676880176147642936080182000000000000)
      constant := (75189985322687057289476914979980593272577737019755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143021901267731761331/25000000000000000000)
  centralHi := (22883504202837081813/4000000000000000000)
  directionLo := (287133497157827703509/50000000000000000000)
  directionHi := (574266994315655407019/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree133.table
  base := (28215326092923355040788905794801453032717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-46253293373741661348200661995697038000000000000)
      constant := (1550124034064244406401387914912025665830627513588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree133.table
  base := (112861304369258976246003373255250477634467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-46378169995419206031089919616706538000000000000)
      constant := (1558224171231817059608542684518512049459072300147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287133497157827703509/50000000000000000000)
  centralHi := (574266994315655407019/100000000000000000000)
  directionLo := (115287628763000413639/20000000000000000000)
  directionHi := (144109535953750517049/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree134.table
  base := (2885376005578865910775835209434459666697/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2283456114028798104946973761158691542000000000000)
      constant := (77122039512365647535211926411518781367619557090920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree134.table
  base := (14426880027632611947044923069303773001199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2289621075667405310870664479501160542000000000000)
      constant := (77524937907686596329317337837437987089832348958328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115287628763000413639/20000000000000000000)
  centralHi := (144109535953750517049/25000000000000000000)
  directionLo := (289300573162858171471/50000000000000000000)
  directionHi := (578601146325716342943/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree135.table
  base := (58997799251350415173209562244416478181307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2300500852744254803832115084528228222000000000000)
      constant := (78296910918485815120003327326916996061684420137526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree135.table
  base := (14749449812612526014342210596337071790301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2306711821559269526217922897783700722000000000000)
      constant := (78705845874677369379665337983500814841786688029672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289300573162858171471/50000000000000000000)
  centralHi := (578601146325716342943/100000000000000000000)
  directionLo := (29037804643859572527/5000000000000000000)
  directionHi := (580756092877191450541/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree136.table
  base := (60301489605335434926254793567587600978371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2317545591459711502717256407897764902000000000000)
      constant := (79480691887516134036796781327362936235981576132678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree136.table
  base := (942210775071268850895393981889618032023/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2323802567451133741565181316066240902000000000000)
      constant := (79895708291339160244089072932021740271903216794496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29037804643859572527/5000000000000000000)
  centralHi := (580756092877191450541/100000000000000000000)
  directionLo := (932644916505866297/160000000000000000)
  directionHi := (291451536408083217813/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree137.table
  base := (15404647793426208654281349835519042696039/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2334590330175168201602397731267301582000000000000)
      constant := (80673382419464396247307732116860400604740810506808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree137.table
  base := (7702323896629883346526551758873957379553/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2340893313342997956912439734348781082000000000000)
      constant := (81094525157679889862778945694247024240433571823632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (932644916505866297/160000000000000000)
  centralHi := (291451536408083217813/50000000000000000000)
  directionLo := (292521086924975819519/50000000000000000000)
  directionHi := (585042173849951639039/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree138.table
  base := (125898207913265897296694424267110642650381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2351635068890624900487539054636838262000000000000)
      constant := (81874982514338478531649121107856618878110541024429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree138.table
  base := (31474551978030238518019546692209471959481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2357984059234862172259698152631321262000000000000)
      constant := (82302296473707546056595080935055251914687531625316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292521086924975819519/50000000000000000000)
  centralHi := (585042173849951639039/100000000000000000000)
  directionLo := (73396685261029610941/12500000000000000000)
  directionHi := (587173482088236887529/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree139.table
  base := (32146513977147516490939574250905940046953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2368679807606081599372680378006374942000000000000)
      constant := (83085492172146299307848783383616377572016702582308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree139.table
  base := (32146513976901404450555783122021193713057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2375074805126726387606956570913861442000000000000)
      constant := (83519022239430142834725575891197423814449656418052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73396685261029610941/12500000000000000000)
  centralHi := (587173482088236887529/100000000000000000000)
  directionLo := (589297082083538788467/100000000000000000000)
  directionHi := (147324270520884697117/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree140.table
  base := (26260145266746588380175532226225065580031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-48688256047378332617506565334202278000000000000)
      constant := (1720508395773383321404131970114790572300415361355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree140.table
  base := (65650363166443266902147264914831182267249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-48819705122828379652126836514212278000000000000)
      constant := (1729483723568483401135667657391493036207349492418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589297082083538788467/100000000000000000000)
  centralHi := (147324270520884697117/25000000000000000000)
  directionLo := (591413056870340883527/100000000000000000000)
  directionHi := (73926632108792610441/12500000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree141.table
  base := (67021109594522116120490622575086536511319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2402769285036994997142963024745448302000000000000)
      constant := (85533240176594829091497527665796356411212072261742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree141.table
  base := (67021109594158272205432368377104345303541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2409256296910454818301473407478941802000000000000)
      constant := (85979337119992148583672222029852452259382804925738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591413056870340883527/100000000000000000000)
  centralHi := (73926632108792610441/12500000000000000000)
  directionLo := (593521488002977923949/100000000000000000000)
  directionHi := (11870429760059558479/2000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree142.table
  base := (136810534474871502724796448555525575842259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2419814023752451696028104348114984982000000000000)
      constant := (86770478523251290196710831122663919217582655649331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree142.table
  base := (68405267237122956904488774700788647341647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2426347042802319033648731825761481982000000000000)
      constant := (87222926234847441440200980426194900887385946903646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593521488002977923949/100000000000000000000)
  centralHi := (11870429760059558479/2000000000000000000)
  directionLo := (595622455592313170873/100000000000000000000)
  directionHi := (297811227796156585437/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree143.table
  base := (139605672191559292736075818041998569948557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2436858762467908394913245671484521662000000000000)
      constant := (88016626432872949556761585142382928952694980724013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree143.table
  base := (139605672191021503767655890990947824740359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2443437788694183248995990244044022162000000000000)
      constant := (88475469799429401182579743180861301058239872832231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595622455592313170873/100000000000000000000)
  centralHi := (297811227796156585437/50000000000000000000)
  directionLo := (149429009585313847379/25000000000000000000)
  directionHi := (597716038341255389517/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree144.table
  base := (17803454042431049621951051423811961299241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2453903501183365093798386994854058342000000000000)
      constant := (89271683905467506067802467636383299664150440993352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree144.table
  base := (71213816169493053796555149808015701220869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2460528534586047464343248662326562342000000000000)
      constant := (89736967813745771857474252315821523564843925133642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149429009585313847379/25000000000000000000)
  centralHi := (597716038341255389517/100000000000000000000)
  directionLo := (299901156789580044137/50000000000000000000)
  directionHi := (23992092543166403531/4000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree145.table
  base := (145276414918875288007690591431104058035727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2470948239898821792683528318223595022000000000000)
      constant := (90535650941042560984561750816026794970021630978543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree145.table
  base := (145276414918477917707500407930982996939081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2477619280477911679690507080609102522000000000000)
      constant := (91007420277804193572937247891802277202697751322729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299901156789580044137/50000000000000000000)
  centralHi := (23992092543166403531/4000000000000000000)
  directionLo := (75235169661894693279/12500000000000000000)
  directionHi := (601881357295157546233/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree146.table
  base := (148152019930171657742470242538632660176801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2487992978614278491568669641593131702000000000000)
      constant := (91808527539605607561966812728555684075748052982209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree146.table
  base := (148152019929830105916789751267993227219449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2494710026369775895037765498891642702000000000000)
      constant := (92286827191612193016235798389164898235053617334041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75235169661894693279/12500000000000000000)
  centralHi := (601881357295157546233/100000000000000000000)
  directionLo := (37747077760653016789/6250000000000000000)
  directionHi := (4831625953363586149/800000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree147.table
  base := (75527223686832029592010936593427738265337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7286034467802607061809316834840000000000000)
      linear := (-1043330994306428650751274870871582000000000000)
      constant := (38771475927182017060338058155589992178677111666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree147.table
  base := (18881805921671312320198455572405218644889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1298442)
      previous := (649221)
      next := (649221)
      square := (7286034467802607061809316834840000000000000)
      linear := (-1046147760208929658635994967586082000000000000)
      constant := (38973422971752259939683900836100754617838084808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37747077760653016789/6250000000000000000)
  centralHi := (4831625953363586149/800000000000000000)
  directionLo := (303009023804802351773/50000000000000000000)
  directionHi := (606018047609604703547/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree148.table
  base := (153983697249673632559754062208082730842363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2522082456045191889338952288332205062000000000000)
      constant := (94381009425725062066043994776152386161204400114267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree148.table
  base := (76991848624710665705742942969106624256399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2528891518153504325732282335456723062000000000000)
      constant := (94872504368506422500943960683345593207071856233182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303009023804802351773/50000000000000000000)
  centralHi := (606018047609604703547/100000000000000000000)
  directionLo := (304037919885458169437/50000000000000000000)
  directionHi := (4864606718167330711/800000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree149.table
  base := (156939769558515902322290508790007608661847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2539127194760648588224093611701741742000000000000)
      constant := (95680614713295852890232706224260598340348263533623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree149.table
  base := (156939769558299071436175081142820026713317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2545982264045368541079540753739263242000000000000)
      constant := (96178774631607081481685025919564031326860784766853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304037919885458169437/50000000000000000000)
  centralHi := (4864606718167330711/800000000000000000)
  directionLo := (305063345797906835439/50000000000000000000)
  directionHi := (610126691595813670879/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree150.table
  base := (19990333037562579192558547851260338588247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2556171933476105287109234935071278422000000000000)
      constant := (96989129563883393339895798100132268313121082169784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree150.table
  base := (2498791629692410851929568716738735537287/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2563073009937232756426799172021803422000000000000)
      constant := (97493999344486169280081554061686335335974108965312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305063345797906835439/50000000000000000000)
  centralHi := (610126691595813670879/100000000000000000000)
  directionLo := (306085336418702495093/50000000000000000000)
  directionHi := (612170672837404990187/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree151.table
  base := (162932381475931737922914827903571644332559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2573216672191561985994376258440815102000000000000)
      constant := (98306553977494549087178071583275929086261639362031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree151.table
  base := (31822730756986642551743545810040309773/1953125000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2580163755829096971774057590304343602000000000000)
      constant := (98818178507150567325119958507426998180636510499840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306085336418702495093/50000000000000000000)
  centralHi := (612170672837404990187/100000000000000000000)
  directionLo := (614207852088158462213/100000000000000000000)
  directionHi := (307103926044079231107/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree152.table
  base := (82984460542553610594811097899787610380109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2590261410907018684879517581810351782000000000000)
      constant := (99632887954136052381981925371534862512371071679962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree152.table
  base := (41492230271242405783786952369458503018549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2597254501720961187121316008586883782000000000000)
      constant := (100151312119607021420284139025012669271274270503764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614207852088158462213/100000000000000000000)
  centralHi := (307103926044079231107/50000000000000000000)
  directionLo := (61623829680676058337/10000000000000000000)
  directionHi := (616238296806760583371/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree153.table
  base := (16903228312831916476145161491019338164791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2607306149622475383764658905179888462000000000000)
      constant := (100968131493814501638314766004616974127548369641190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree153.table
  base := (169032283128200931789786506862425310864173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2614345247612825402468574426869423962000000000000)
      constant := (101493400181862141637327644930146359535560330020557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61623829680676058337/10000000000000000000)
  centralHi := (616238296806760583371/100000000000000000000)
  directionLo := (309131036672090383691/50000000000000000000)
  directionHi := (618262073344180767383/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree154.table
  base := (86061233802926867903239059547472660917609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-53558181394651675156118372011212758000000000000)
      constant := (2088005808092578809413185328267713608124230741938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree154.table
  base := (172122467605752146825680838364086321489783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-53702775377646726894200670309223758000000000000)
      constant := (2098866177426987812405296688690304168745971044103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309131036672090383691/50000000000000000000)
  centralHi := (618262073344180767383/100000000000000000000)
  directionLo := (620279246968970553957/100000000000000000000)
  directionHi := (310139623484485276979/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree155.table
  base := (87619737258995610296398088072289194146257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2641395627053388781534941551918961822000000000000)
      constant := (103665347262307964400380969147748823956121678406626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree155.table
  base := (1752394745179039362162407216848847908273/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2648526739396553833163091263434504322000000000000)
      constant := (104204439655794145504593132683544975258542651745700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620279246968970553957/100000000000000000000)
  centralHi := (310139623484485276979/50000000000000000000)
  directionLo := (622289881891824731379/100000000000000000000)
  directionHi := (31114494094591236569/5000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree156.table
  base := (178383303865006076873086257560064979513203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2658440365768845480420082875288498502000000000000)
      constant := (105027319491135510133280354498312256564767584591827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree156.table
  base := (178383303864931085973856611219440893384673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2665617485288418048510349681717044502000000000000)
      constant := (105573391067483577420807416610049526419421188205057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622289881891824731379/100000000000000000000)
  centralHi := (31114494094591236569/5000000000000000000)
  directionLo := (312147020644715260949/50000000000000000000)
  directionHi := (624294041289430521899/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree157.table
  base := (45388488911791750421686814477917878131169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2675485104484302179305224198658035182000000000000)
      constant := (106398201283025068997179570918635204383488568238084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree157.table
  base := (7262158225884103016815216677948832869451/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2682708231180282263857608099999584682000000000000)
      constant := (106951296928996775070783159920385754836331584151475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312147020644715260949/50000000000000000000)
  centralHi := (624294041289430521899/100000000000000000000)
  directionLo := (78286473415953736369/12500000000000000000)
  directionHi := (626291787327629890953/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree158.table
  base := (92375714932368505763831559927111174450739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2692529843199758878190365522027571862000000000000)
      constant := (107777992637982582800059099002188288458034429611302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree158.table
  base := (92375714932340831890956943429865083356767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2699798977072146479204866518282124862000000000000)
      constant := (108338157240339685746066560238243835694796947015806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78286473415953736369/12500000000000000000)
  centralHi := (626291787327629890953/100000000000000000000)
  directionLo := (628283181183919005309/100000000000000000000)
  directionHi := (62828318118391900531/10000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree159.table
  base := (93987863258986766152074557035383720483601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2709574581915215577075506845397108542000000000000)
      constant := (109166693556013867052930522203809726408797029086818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree159.table
  base := (37595145303585197135859422238998482014627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2716889722964010694552124936564665042000000000000)
      constant := (109733972001518129672695727629853429153893883443215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628283181183919005309/100000000000000000000)
  centralHi := (62828318118391900531/10000000000000000000)
  directionLo := (78783535383663484797/12500000000000000000)
  directionHi := (630268283069307878377/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree160.table
  base := (191226845607128496924648681116193129734767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2726619320630672275960648168766645222000000000000)
      constant := (110564304037124613174395882465065920559576288909903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree160.table
  base := (47806711401771913368155011600067465309769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2733980468855874909899383354847205222000000000000)
      constant := (111138741212537802323266465542090359557680717067684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78783535383663484797/12500000000000000000)
  centralHi := (630268283069307878377/100000000000000000000)
  directionLo := (126449430449912460107/20000000000000000000)
  directionHi := (79030894031195287567/12500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree161.table
  base := (194504787132448448688851489541049519481391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-55993144068288346425424275349717998000000000000)
      constant := (2285118858802456955639946097661007454511219988031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree161.table
  base := (97252393566206682373432162528064713044343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-56144310505055900515237587206729498000000000000)
      constant := (2296989079049066874390640251049324634733353882126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126449430449912460107/20000000000000000000)
  centralHi := (79030894031195287567/12500000000000000000)
  directionLo := (126843969413169851203/20000000000000000000)
  directionHi := (39638740441615578501/6250000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree162.table
  base := (98904775547087324479029675025733074221327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2760708798061585673730930815505718582000000000000)
      constant := (113386253688606650346399472622158529296663332497886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree162.table
  base := (197809551094144513505019745347839993001043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2768161960639603340593900191412285582000000000000)
      constant := (113975142984123006572414536465544664911446499422387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126843969413169851203/20000000000000000000)
  centralHi := (39638740441615578501/6250000000000000000)
  directionLo := (636186424954806173147/100000000000000000000)
  directionHi := (159046606238701543287/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree163.table
  base := (100570568746271593914251527123836983715233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2777753536777042372616072138875255262000000000000)
      constant := (114810592858988725248010984654491354448287364280194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree163.table
  base := (100570568746258651936021638367663853334193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2785252706531467555941158609694825762000000000000)
      constant := (115406775544699327594598698056155549660294868141474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636186424954806173147/100000000000000000000)
  centralHi := (159046606238701543287/25000000000000000000)
  directionLo := (319073471234026769841/50000000000000000000)
  directionHi := (638146942468053539683/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree164.table
  base := (102249773163892548371724731584981326684727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2794798275492499071501213462244791942000000000000)
      constant := (116243841592471834764606019529550774179933215639086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree164.table
  base := (204499546327762865314092374625734722883157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2802343452423331771288417027977365942000000000000)
      constant := (116847362555138461359543985343769408454265905735413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319073471234026769841/50000000000000000000)
  centralHi := (638146942468053539683/100000000000000000000)
  directionLo := (640101455291169637153/100000000000000000000)
  directionHi := (320050727645584818577/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree165.table
  base := (12992798600007903884994603777230843824179/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2811843014207955770386354785614328622000000000000)
      constant := (117685999889061086417369783114472350061553955305776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree165.table
  base := (103942388800053684273951159253205067071897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2819434198315195986635675446259906122000000000000)
      constant := (118296904015445517291947701477902460028133657548146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (640101455291169637153/100000000000000000000)
  centralHi := (320050727645584818577/50000000000000000000)
  directionLo := (642050018262145406073/100000000000000000000)
  directionHi := (321025009131072703037/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree166.table
  base := (13206051956861783721147862099725784730267/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2828887752923412469271496108983865302000000000000)
      constant := (119137067748761478590401055656806313947976389910448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree166.table
  base := (4225936626195442829190743332660432221909/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2836524944207060201982933864542446302000000000000)
      constant := (119755399925625495412075870573185017030451810809050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642050018262145406073/100000000000000000000)
  centralHi := (321025009131072703037/50000000000000000000)
  directionLo := (321996342694668372617/50000000000000000000)
  directionHi := (128798537077867349047/20000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree167.table
  base := (6710490858030870845408034690871249551923/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2845932491638869168156637432353401982000000000000)
      constant := (120597045171577903099543190656141189335999630729824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree167.table
  base := (107367853728486892236951814892672925904993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2853615690098924417330192282824986482000000000000)
      constant := (121222850285683288942076963957003411865352060015874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321996342694668372617/50000000000000000000)
  centralHi := (128798537077867349047/20000000000000000000)
  directionLo := (322964754934465435931/50000000000000000000)
  directionHi := (645929509868930871863/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree168.table
  base := (43640281208387275705989717059083323593781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-58428106741925017694730178688223238000000000000)
      constant := (2491141472602349953954405651829507316965001930105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree168.table
  base := (21820140604192428491968296511802343192603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (63623658)
      previous := (31811829)
      next := (31811829)
      square := (357015688922327746028656524907160000000000000)
      linear := (-58585845632465074136274504104235238000000000000)
      constant := (2504066430522932385502063385058560085078608797230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell051.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322964754934465435931/50000000000000000000)
  centralHi := (645929509868930871863/100000000000000000000)
  directionLo := (161965136025485680787/25000000000000000000)
  directionHi := (647860544101942723149/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree169.table
  base := (11084696353242075760583154640079217078469/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2880021969069782565926920079092475342000000000000)
      constant := (123543728706577898830048179029403372757652937704420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree169.table
  base := (221693927064831130021526600385802789275481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3117559242)
      previous := (1558779621)
      next := (1558779621)
      square := (17493768757194059555404169720450840000000000000)
      linear := (-2887797181882652848024709119390066842000000000000)
      constant := (124184614355451376600407781732053485692747494750329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell051.Kernel169
