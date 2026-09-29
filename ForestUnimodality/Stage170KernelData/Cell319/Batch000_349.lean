import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell319.Parameters
import ForestUnimodality.BinomialMassData.Q236_371.Batch000_049
import ForestUnimodality.BinomialMassData.Q236_371.Batch050_099
import ForestUnimodality.BinomialMassData.Q236_371.Batch100_149
import ForestUnimodality.BinomialMassData.Q9_14.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_14.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_14.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree000.table
  base := (3264727133522006855268493613/250000000000000000000000000)
  polynomial :=
    { denominator := 927500000000000000000000000000000000000000
      center := (2124)
      previous := (0)
      next := (1215)
      square := (10681839438851181926098954775000000000000)
      linear := (-27189770194671160673596799170000000000000)
      constant := (12112137665366645433046111304230000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree000.table
  base := (3264727133522006855268493613/250000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-1026029063949855119758369780000000000000)
      constant := (457061798693080959737589105820000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree001.table
  base := (106194201067642427171469178352430664046323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-60516931829443033916092476583480000000000000)
      constant := (14648757573610140952512970296024989029999944043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree001.table
  base := (105937378203214589433273248188010178871121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-21619995948102548079250429220000000000000)
      constant := (5202497947157179335009060891757498764684929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (23957871187497746747/50000000000000000000)
  directionHi := (9583148474999098699/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree002.table
  base := (43161201279296714476695043884198371560799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-40342122344997032696283651599340000000000000)
      constant := (5979246851137448770020469393684628059999935159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree002.table
  base := (85905237228350488139606519495777392782673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-28875585000907124481883681520000000000000)
      constant := (4237153761836734337799755721433092246350977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23957871187497746747/50000000000000000000)
  centralHi := (9583148474999098699/20000000000000000000)
  directionLo := (16940773179473460707/25000000000000000000)
  directionHi := (67763092717893842829/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree003.table
  base := (70139127094038070758603217666670370286577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-100851557550545096869042129813880000000000000)
      constant := (9788750634096803351072683278122016436614744857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree003.table
  base := (8703841331800958295721681067290319705149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-18065587026855850442258466910000000000000)
      constant := (1730298984704831775231996292581402662209204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16940773179473460707/25000000000000000000)
  centralHi := (67763092717893842829/100000000000000000000)
  directionLo := (10374062534484152371/12500000000000000000)
  directionHi := (82992500275873218969/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree004.table
  base := (14238475235491341585526510363062467415793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-30254717602774032086379239107270000000000000)
      constant := (2011122718532033556964952751305161077577164313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree004.table
  base := (56402949287217986272016496688932620719239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-43386763106516277287150186120000000000000)
      constant := (2837996019361728218853652090237698415242711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10374062534484152371/12500000000000000000)
  centralHi := (82992500275873218969/100000000000000000000)
  directionLo := (23957871187497746747/25000000000000000000)
  directionHi := (95831484749990986989/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree005.table
  base := (2887128523128784221821304091601083435179/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-35296545817911789955497945761070000000000000)
      constant := (1661722965756338291703329563918858900405890956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree005.table
  base := (22817035758532173661523154301317555665517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-25321176079660426844891719210000000000000)
      constant := (1170272326408395208369777912377060227610333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23957871187497746747/25000000000000000000)
  centralHi := (95831484749990986989/100000000000000000000)
  directionLo := (107142857142857142857/100000000000000000000)
  directionHi := (53571428571428571429/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree006.table
  base := (37406218093138286585882503873132249196053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-161353496132198191298466609659480000000000000)
      constant := (5533550573160266465063312626158275911593930973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree006.table
  base := (2303723527858751556728105449453312661011/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-28948970606062715046208345360000000000000)
      constant := (972741172881360319086128565695698563116312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107142857142857142857/100000000000000000000)
  centralHi := (53571428571428571429/50000000000000000000)
  directionLo := (117369119465392738597/100000000000000000000)
  directionHi := (58684559732696369299/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree007.table
  base := (15110891135534204442809654807197428038167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (225144)
      previous := (0)
      next := (128790)
      square := (1132274980518225284166489206150000000000000)
      linear := (-12965772070910658769638674019620000000000000)
      constant := (332409428812394054648074021687763027514477721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree007.table
  base := (14851371863317533867849990498317391435343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-4653823590352143321074995930000000000000)
      constant := (116739271515402233566825006335721740047401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117369119465392738597/100000000000000000000)
  centralHi := (58684559732696369299/50000000000000000000)
  directionLo := (63386569104638743313/50000000000000000000)
  directionHi := (126773138209277486627/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree008.table
  base := (24341398496447842363340895186193555329599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-201688121853300254251416262889880000000000000)
      constant := (3966233264239737821989574541757107149121335959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree008.table
  base := (23858384539270717528524833160070364623649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-72409119317734582897683195320000000000000)
      constant := (1392192766972063156374489210603447866558801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63386569104638743313/50000000000000000000)
  centralHi := (126773138209277486627/100000000000000000000)
  directionLo := (135526185435787685657/100000000000000000000)
  directionHi := (67763092717893842829/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree009.table
  base := (19521987893371020645058022692778419540427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-221855434713851285727891089505080000000000000)
      constant := (3437596736200411574530674647334634443963912707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree009.table
  base := (3815857061928968436912947941125379613317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-79664708370539159300316447620000000000000)
      constant := (1206897777905911824512658802280718005262665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135526185435787685657/100000000000000000000)
  centralHi := (67763092717893842829/50000000000000000000)
  directionLo := (143747227124986480483/100000000000000000000)
  directionHi := (35936806781246620121/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree010.table
  base := (155661417712807659448868535627939784723/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-60505686893600579301091479030070000000000000)
      constant := (760162722419639378767374798890331497726461075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree010.table
  base := (15165168480674306692229404151685911713571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-86920297423343735702949699920000000000000)
      constant := (1068651233720103658782134336132609673964979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143747227124986480483/100000000000000000000)
  centralHi := (35936806781246620121/25000000000000000000)
  directionLo := (151522881682831612371/100000000000000000000)
  directionHi := (37880720420707903093/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree011.table
  base := (12313507800320499319543386711222321236927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-262190060434953348680840742735480000000000000)
      constant := (2753324669640386261273494993094231517371869207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree011.table
  base := (11953746062234114223733790859043458723331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-94175886476148312105582952220000000000000)
      constant := (969501022898513814621449065838129477443219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151522881682831612371/100000000000000000000)
  centralHi := (37880720420707903093/25000000000000000000)
  directionLo := (620775543004659287/390625000000000000)
  directionHi := (158918539009192777473/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree012.table
  base := (9633801065900785466382267926896347219847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-282357373295504380157315569350680000000000000)
      constant := (2557685530156893348651252840954100127686960927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree012.table
  base := (2328369761310665295071369135619988444301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-50715737764476444254108102260000000000000)
      constant := (451500866998071857844887125210758867541498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620775543004659287/390625000000000000)
  centralHi := (158918539009192777473/100000000000000000000)
  directionLo := (10374062534484152371/6250000000000000000)
  directionHi := (165985000551746437937/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree013.table
  base := (7421136032002164089303092935296261552493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-302524686156055411633790395965880000000000000)
      constant := (2439159280164824242587216994391752736346689013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree013.table
  base := (1427543975409126830423614115556431444359/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-108687064581757464910849456820000000000000)
      constant := (863927636932932004908556749296325703867955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10374062534484152371/6250000000000000000)
  centralHi := (165985000551746437937/100000000000000000000)
  directionLo := (86381333017484460561/50000000000000000000)
  directionHi := (172762666034968921123/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree014.table
  base := (1397357571195995391990998940666220488263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (112572)
      previous := (0)
      next := (64395)
      square := (566137490259112642083244603075000000000000)
      linear := (-11524714250593087253938043663610000000000000)
      constant := (85210623219312054932996881389759893460715369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree014.table
  base := (1334993570936754445759595915197796336743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-8281618116754431522391622080000000000000)
      constant := (60574322306283852130309306182769148714402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86381333017484460561/50000000000000000000)
  centralHi := (172762666034968921123/100000000000000000000)
  directionLo := (35856858280031809199/20000000000000000000)
  directionHi := (44821072850039761499/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree015.table
  base := (4068677304214033860177674796744814150563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-342859311877157474586740049196280000000000000)
      constant := (2388264272660880638690637513305952964497641883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree015.table
  base := (1925034205585130092102588127025387878827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-61599121343683308858057980710000000000000)
      constant := (425950920603309223941937062436744006062523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35856858280031809199/20000000000000000000)
  centralHi := (44821072850039761499/25000000000000000000)
  directionLo := (185576872239522567163/100000000000000000000)
  directionHi := (46394218059880641791/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree016.table
  base := (1400961841047627848883779131540497513519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-181513312368854253031607437905740000000000000)
      constant := (1219210311833800641855149990981005618258268679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree016.table
  base := (1305524001652604806074497748404112665641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-65226915870085597059374606860000000000000)
      constant := (436360432572184061828592537031801520616409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185576872239522567163/100000000000000000000)
  centralHi := (46394218059880641791/25000000000000000000)
  directionLo := (191662969499981973977/100000000000000000000)
  directionHi := (95831484749990986989/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree017.table
  base := (871408665873137832215747862524451655151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-191596968799129768769844851213340000000000000)
      constant := (1264993277798994415035827898317008050266638791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree017.table
  base := (394167366681653916832566012743321346973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-68854710396487885260691233010000000000000)
      constant := (454115824011692843783411922281345492003354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191662969499981973977/100000000000000000000)
  centralHi := (95831484749990986989/50000000000000000000)
  directionLo := (197561666941990442357/100000000000000000000)
  directionHi := (98780833470995221179/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree018.table
  base := (213404631110726620243816920583311151931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-100840312614702642254041132260470000000000000)
      constant := (664441883612679354119783347769767530262934771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree018.table
  base := (709369513665346858708909698297992100723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-144965009845780346924015718320000000000000)
      constant := (956593588742983696551826897676601612935427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197561666941990442357/100000000000000000000)
  centralHi := (98780833470995221179/50000000000000000000)
  directionLo := (40657855630736305697/20000000000000000000)
  directionHi := (101644639076840764243/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree019.table
  base := (51793051101213155262780915433429739043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-211764281659680800246319677828540000000000000)
      constant := (1408766158249943613291826593226532702711617563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree019.table
  base := (-2137820480195869125823596516269915139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-76110299449292461663324485310000000000000)
      constant := (508155448102958709306289490806013870790945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40657855630736305697/20000000000000000000)
  centralHi := (101644639076840764243/50000000000000000000)
  directionLo := (10442993940866747043/5000000000000000000)
  directionHi := (208859878817334940861/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree020.table
  base := (-532332155121527411495780158376995519553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-443695876179912631969114182272280000000000000)
      constant := (3005832689112332770634112892190431959693205527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree020.table
  base := (-640393504195034051046513356386903875513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-159476187951389499729282222920000000000000)
      constant := (1086167399451719933393788415937041710099863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10442993940866747043/5000000000000000000)
  centralHi := (208859878817334940861/100000000000000000000)
  directionLo := (107142857142857142857/50000000000000000000)
  directionHi := (42857142857142857143/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree021.table
  base := (-1074562556852785034409371615233710821859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (450288)
      previous := (0)
      next := (257580)
      square := (2264549961036450568332978412300000000000000)
      linear := (-66266169862923380492227001269640000000000000)
      constant := (459979593520916102217096281279899544109786483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree021.table
  base := (-291966736736140382807531369185866935233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-11909412643156719723708248230000000000000)
      constant := (83226697208663414834094232398897862906738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107142857142857142857/50000000000000000000)
  centralHi := (42857142857142857143/20000000000000000000)
  directionLo := (109788758206709982677/50000000000000000000)
  directionHi := (43915503282683993071/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree022.table
  base := (-1539768555499557687038593175120578493073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-484030501901014694922063835502680000000000000)
      constant := (3457312138835444373257957482720188455634939207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree022.table
  base := (-1620232364617467133936948685670781142993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-173987366056998652534548727520000000000000)
      constant := (1252524722867841667358905552942131723993343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109788758206709982677/50000000000000000000)
  centralHi := (43915503282683993071/20000000000000000000)
  directionLo := (224744753179318188641/100000000000000000000)
  directionHi := (112372376589659094321/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree023.table
  base := (-242693952263591205231605992836074905953/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-126049453690391431599634665529470000000000000)
      constant := (929081380538406886425500580186459627739446254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree023.table
  base := (-2010873721171039533911785646329167757877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-181242955109803228937181979820000000000000)
      constant := (1347564471057474367376051983514870779864027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224744753179318188641/100000000000000000000)
  centralHi := (112372376589659094321/50000000000000000000)
  directionLo := (114897913872467231837/50000000000000000000)
  directionHi := (9191833109797378547/4000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree024.table
  base := (-458204108436972061935701237402861159547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-524365127622116757875013488733080000000000000)
      constant := (3995368278603637170986256052830283935693956865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree024.table
  base := (-2350697927251769014496104615189523790773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-188498544162607805339815232120000000000000)
      constant := (1449758566868507883845026600735713334252123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114897913872467231837/50000000000000000000)
  centralHi := (9191833109797378547/4000000000000000000)
  directionLo := (46947647786157095439/20000000000000000000)
  directionHi := (58684559732696369299/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree025.table
  base := (-519450808111393169961249942778636441363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-544532440482667789351488315348280000000000000)
      constant := (4293190805072974635929789944542028507871776585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree025.table
  base := (-2648599163679094082274046891307439272553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-195754133215412381742448484420000000000000)
      constant := (1558671195440789729943206480950935475644903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46947647786157095439/20000000000000000000)
  centralHi := (58684559732696369299/25000000000000000000)
  directionLo := (14973669492186091717/6250000000000000000)
  directionHi := (239578711874977467473/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree026.table
  base := (-2867676718500787854517729082463024296781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-564699753343218820827963141963480000000000000)
      constant := (4608771171466881592029365331270786872766766379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree026.table
  base := (-2911835381536138052822990795055965686487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-203009722268216958145081736720000000000000)
      constant := (1673946717171246863207300086462257681362137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14973669492186091717/6250000000000000000)
  centralHi := (239578711874977467473/100000000000000000000)
  directionLo := (122161652689193354907/50000000000000000000)
  directionHi := (48864661075677341963/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree027.table
  base := (-1554182378841028637605948302794410886267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-292433533101884926152218984289340000000000000)
      constant := (2470636523032352582701739508860754491203323853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree027.table
  base := (-629266738734546283704786073924920187759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-210265311321021534547714989020000000000000)
      constant := (1795294703530237589510638709153394553999045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122161652689193354907/50000000000000000000)
  centralHi := (48864661075677341963/20000000000000000000)
  directionLo := (31122187603452457113/12500000000000000000)
  directionHi := (49795500165523931381/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree028.table
  base := (-3324294535464850203360024077917277631489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (450288)
      previous := (0)
      next := (257580)
      square := (2264549961036450568332978412300000000000000)
      linear := (-86433482723474411968701827884840000000000000)
      constant := (755715925044239508392276240401032569932031793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree028.table
  base := (-839234544428152472409942895754177637239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-15537207169559007925024874380000000000000)
      constant := (137319842479585632789309996899441513078654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31122187603452457113/12500000000000000000)
  centralHi := (49795500165523931381/20000000000000000000)
  directionLo := (63386569104638743313/25000000000000000000)
  directionHi := (253546276418554973253/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree029.table
  base := (-439943113433999748646712917392223209717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-156300422981217978814346905452270000000000000)
      constant := (1413606260358753410545563903530314010382684806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree029.table
  base := (-3547611028282678743959190549456174448081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-224776489426630687352981493620000000000000)
      constant := (2055301843186412313214758699181647452044031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63386569104638743313/25000000000000000000)
  centralHi := (253546276418554973253/100000000000000000000)
  directionLo := (258034169545549188859/100000000000000000000)
  directionHi := (12901708477277459443/5000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree030.table
  base := (-3697461854760849559953647626935198334759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-645369004785422946733862448424280000000000000)
      constant := (6034053200262001852009847340915412366005436481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree030.table
  base := (-744319181712885706865539356495232734791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-232032078479435263755614745920000000000000)
      constant := (2193607909450984914914464970758667979976205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258034169545549188859/100000000000000000000)
  centralHi := (12901708477277459443/5000000000000000000)
  directionLo := (65611332395977984773/25000000000000000000)
  directionHi := (262445329583911939093/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree031.table
  base := (-193039627725691343091760840842093077957/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-166384079411493494552584318759870000000000000)
      constant := (1607129456894018862285172948640387333284602815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree031.table
  base := (-485193832928139760671040128367361771681/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-119643833766119920079123999110000000000000)
      constant := (1168632879554710490871465132412497092750524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65611332395977984773/25000000000000000000)
  centralHi := (262445329583911939093/100000000000000000000)
  directionLo := (10671342512561770607/4000000000000000000)
  directionHi := (33347945351755533147/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree032.table
  base := (-802358920359487217648488046723644010013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-685703630506525009686812101654680000000000000)
      constant := (6837508185734685454605712154770314574089003335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree032.table
  base := (-1007413797898662784035627657146567757327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-123271628292522208280440625260000000000000)
      constant := (1243084288561977615243071830719636359781954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671342512561770607/4000000000000000000)
  centralHi := (33347945351755533147/12500000000000000000)
  directionLo := (135526185435787685657/50000000000000000000)
  directionHi := (54210474174315074263/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree033.table
  base := (-129760157207682226762253081641951020679/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-176467735841769010290821732067470000000000000)
      constant := (1815192167679084218830293376089321756501774088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree033.table
  base := (-833539834126785872958018607614846420077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-253798845637848992963514502820000000000000)
      constant := (2640228669294103478915253615519362627081135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135526185435787685657/50000000000000000000)
  centralHi := (54210474174315074263/20000000000000000000)
  directionLo := (137627491914269239501/50000000000000000000)
  directionHi := (275254983828538479003/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree034.table
  base := (-2141956453818871685383453088181689534489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-363019128113813536319880877442540000000000000)
      constant := (3849044410134033298549535287494544070783399551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree034.table
  base := (-4297153435722031547055010485419027780827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-261054434690653569366147755120000000000000)
      constant := (2799373964696090867018806957794467638739477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137627491914269239501/50000000000000000000)
  centralHi := (275254983828538479003/100000000000000000000)
  directionLo := (8731074649824975957/3125000000000000000)
  directionHi := (447031022071038769/160000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree035.table
  base := (-4407818561515066343477374521009310116687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (450288)
      previous := (0)
      next := (257580)
      square := (2264549961036450568332978412300000000000000)
      linear := (-106600795584025443445176654500040000000000000)
      constant := (1164185023068787371426085777155793935175583519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree035.table
  base := (-4419228091121951344506472976194668052327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (162)
      previous := (0)
      next := (90)
      square := (806176561422730711403694700000000000000)
      linear := (-38330003391922592252683001060000000000000)
      constant := (423363595460147243625701771141637323633711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8731074649824975957/3125000000000000000)
  centralHi := (447031022071038769/160000000000000000)
  directionLo := (28347335475692042041/10000000000000000000)
  directionHi := (283473354756920420411/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree036.table
  base := (-2262540968428937959692680576390055041659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-383186440974364567796355704057740000000000000)
      constant := (4307122277672362839186616085318536434011013581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree036.table
  base := (-4534919848886057494761636882944944703447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-275565612796262722171414259720000000000000)
      constant := (3132693440978356925855329273855697709531097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28347335475692042041/10000000000000000000)
  centralHi := (283473354756920420411/100000000000000000000)
  directionLo := (143747227124986480483/50000000000000000000)
  directionHi := (287494454249972960967/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree037.table
  base := (-2318281046483500908988249481647287598693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-393270097404640083534593117365340000000000000)
      constant := (4546409380038241664425621884896665687628296787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree037.table
  base := (-929010123305275470289711309882985611343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-282821201849067298574047512020000000000000)
      constant := (3306778509499980188117282922543668525220965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143747227124986480483/50000000000000000000)
  centralHi := (287494454249972960967/100000000000000000000)
  directionLo := (36432510291255651817/12500000000000000000)
  directionHi := (291460082330045214537/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree038.table
  base := (-74108898286289656846993612534911957113/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-201676876917457799636415265336470000000000000)
      constant := (2396229996796460983326555470367474932976153072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree038.table
  base := (-237514948633173311524906483780254975741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-145038395450935937488340382160000000000000)
      constant := (1742883561716746640842579678377675061886910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36432510291255651817/12500000000000000000)
  centralHi := (291460082330045214537/100000000000000000000)
  directionLo := (295372473259076180741/100000000000000000000)
  directionHi := (147686236629538090371/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree039.table
  base := (-1211223099901428166403332423504718156419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-206718705132595557505533971990270000000000000)
      constant := (2522616816626993144204271497065467088232332421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree039.table
  base := (-4851225859837654700361998291127632247491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-297332379954676451379314016620000000000000)
      constant := (3669631796594420008704828117039746019872941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295372473259076180741/100000000000000000000)
  centralHi := (147686236629538090371/50000000000000000000)
  directionLo := (149616857611810083963/50000000000000000000)
  directionHi := (299233715223620167927/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree040.table
  base := (-4942818518779411841232196832535098694973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-847042133390933261498610714576280000000000000)
      constant := (10609393470807559648045158334992236480525221307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree040.table
  base := (-4948295572782050484929398130139562818681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-304587969007481027781947268920000000000000)
      constant := (3858349778540838090705716652423161421884631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149616857611810083963/50000000000000000000)
  centralHi := (299233715223620167927/100000000000000000000)
  directionLo := (303045763365663224743/100000000000000000000)
  directionHi := (37880720420707903093/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree041.table
  base := (-5037152681170615243629224970062740045339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-867209446251484292975085541191480000000000000)
      constant := (11141642878420646337053069303660874397419494701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree041.table
  base := (-1008378583450806364057783008617518728747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-311843558060285604184580521220000000000000)
      constant := (4051902213790635994119484256233707911456985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303045763365663224743/100000000000000000000)
  centralHi := (37880720420707903093/12500000000000000000)
  directionLo := (306810451355921853309/100000000000000000000)
  directionHi := (30681045135592185331/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree042.table
  base := (-128205784325351352360993860789687256629/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (112572)
      previous := (0)
      next := (64395)
      square := (566137490259112642083244603075000000000000)
      linear := (-31692027111144118730412870278810000000000000)
      constant := (417398899108764214420132464878443794729039730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree042.table
  base := (-1026467449979217888751675554312436929913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (162)
      previous := (0)
      next := (90)
      square := (806176561422730711403694700000000000000)
      linear := (-45585592444727168655316253360000000000000)
      constant := (607181921981190238973936760019064707453045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306810451355921853309/100000000000000000000)
  centralHi := (30681045135592185331/10000000000000000000)
  directionLo := (38816187713007424751/12500000000000000000)
  directionHi := (310529501704059398009/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree043.table
  base := (-2608167322655312765249760445076541759529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-453772035986293177964017597210940000000000000)
      constant := (6122966907091000082682934990012739715676668911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree043.table
  base := (-1304973494046736011659555031820444173591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-163177368082947378494923512910000000000000)
      constant := (2226725246952733906463107293674096470988082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38816187713007424751/12500000000000000000)
  centralHi := (310529501704059398009/100000000000000000000)
  directionLo := (314204534970325288821/100000000000000000000)
  directionHi := (157102267485162644411/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree044.table
  base := (-5301695896299070401887080532223728053801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-927711384833137387404510021037080000000000000)
      constant := (12817904670663474292513889641886913846946776559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree044.table
  base := (-1326195993849608295777213870339779421627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-166805162609349666696240139060000000000000)
      constant := (2330711255408862187145307901346701616680554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314204534970325288821/100000000000000000000)
  centralHi := (157102267485162644411/50000000000000000000)
  directionLo := (620775543004659287/195312500000000000)
  directionHi := (63567415603677110989/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree045.table
  base := (-673063739076431706657775489479514550979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-236969674423422104720246211913070000000000000)
      constant := (3350763733465749083539963130700500275377398922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree045.table
  base := (-1346797833445040312907786516620607211443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-170432957135751954897556765210000000000000)
      constant := (2437090242189435370693089358383680493278586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620775543004659287/195312500000000000)
  centralHi := (63567415603677110989/20000000000000000000)
  directionLo := (321428571428571428571/100000000000000000000)
  directionHi := (80357142857142857143/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree046.table
  base := (-5464939485452558775212783696669622938187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-968046010554239450357459674267480000000000000)
      constant := (14001362197036348685875750489750376429165003133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree046.table
  base := (-2733634848030087093854848746728677399463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-174060751662154243098873391360000000000000)
      constant := (2545858442998616331686588827320294807426313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321428571428571428571/100000000000000000000)
  centralHi := (80357142857142857143/25000000000000000000)
  directionLo := (5077818377713091889/1562500000000000000)
  directionHi := (324980376173637880897/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree047.table
  base := (-692890107475671275043148178423507530239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-247053330853697620458483625220670000000000000)
      constant := (3653201926821957096843302695424460000060747602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree047.table
  base := (-693143435953461561010318324738507176569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-177688546188556531300190017510000000000000)
      constant := (2657012711414369167955724405683752593392476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5077818377713091889/1562500000000000000)
  centralHi := (324980376173637880897/100000000000000000000)
  directionLo := (164246889822384553463/50000000000000000000)
  directionHi := (328493779644769106927/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree048.table
  base := (-5619168227201347937189364976370425318757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1008380636275341513310409327497880000000000000)
      constant := (15237375747180853751618161742964838288700967763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree048.table
  base := (-2810466106453126921963104503007603784877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-181316340714958819501506643660000000000000)
      constant := (2770550413578317206066671460632627414541027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164246889822384553463/50000000000000000000)
  centralHi := (328493779644769106927/100000000000000000000)
  directionLo := (10374062534484152371/3125000000000000000)
  directionHi := (331970001103492875873/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree049.table
  base := (-2846588716981443007767196592168843353331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (225144)
      previous := (0)
      next := (128790)
      square := (1132274980518225284166489206150000000000000)
      linear := (-73467710652563753199063153865220000000000000)
      constant := (1133932366023697438711171848140264033143452547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree049.table
  base := (-711839249671452561219080244436436952181/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-26420590748765872528974752830000000000000)
      constant := (412352763059472038753412434263279765338932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10374062534484152371/3125000000000000000)
  centralHi := (331970001103492875873/100000000000000000000)
  directionLo := (335410196624968454461/100000000000000000000)
  directionHi := (167705098312484227231/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree050.table
  base := (-5765229045369424612806480111548551258511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1048715261996443576263358980728280000000000000)
      constant := (16525828749654932132926822195790345856227287449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree050.table
  base := (-5766568509750647893888544087566894541549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-377143859535526791808279791920000000000000)
      constant := (6009535282089044809206734053209222167464099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335410196624968454461/100000000000000000000)
  centralHi := (167705098312484227231/50000000000000000000)
  directionLo := (169407731794734607071/50000000000000000000)
  directionHi := (338815463589469214143/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree051.table
  base := (-5835390880573896222199087227748682817371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1068882574856994607739833807343480000000000000)
      constant := (17189693288454328943233769478287523548334238189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree051.table
  base := (-1167311875160986435954746138303167011021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-384399448588331368210913044220000000000000)
      constant := (6250887507263625002061671892660724082299855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169407731794734607071/50000000000000000000)
  centralHi := (338815463589469214143/100000000000000000000)
  directionLo := (68437368954305622853/20000000000000000000)
  directionHi := (171093422385764057133/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree052.table
  base := (-5903720112211607961446735791628952479491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1089049887717545639216308633958680000000000000)
      constant := (17866638871431258265885150480887759351770379269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree052.table
  base := (-5904740174663396607534799238016396739749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-391655037641135944613546296520000000000000)
      constant := (6496992732979031881366384321977196559752299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68437368954305622853/20000000000000000000)
  centralHi := (171093422385764057133/50000000000000000000)
  directionLo := (86381333017484460561/25000000000000000000)
  directionHi := (69105066413987568449/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree053.table
  base := (-238810600304550971520465670885791632043/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25970000000000000000000000000000000000000000
      center := (59472)
      previous := (0)
      next := (34020)
      square := (299091504287833093930770733700000000000000)
      linear := (-20928626426001823975335536991960000000000000)
      constant := (350125638773999705881913364819019978289608225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree053.table
  base := (-2985578046017928475241299395087297657057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-199455313346970260508089774410000000000000)
      constant := (3373924372567742237114319868533222414804207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86381333017484460561/25000000000000000000)
  centralHi := (69105066413987568449/20000000000000000000)
  directionLo := (21801991869776392483/6250000000000000000)
  directionHi := (348831869916422279729/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree054.table
  base := (-6035066374643754410435538219149009795357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1129384513438647702169258287189080000000000000)
      constant := (19259747622391386755979650363133631142757267163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree054.table
  base := (-1207169058219599265776043248290578751943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-406166215746745097418812801120000000000000)
      constant := (7003453673737374307755546880148808205773965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21801991869776392483/6250000000000000000)
  centralHi := (348831869916422279729/100000000000000000000)
  directionLo := (352107358396178215793/100000000000000000000)
  directionHi := (176053679198089107897/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree055.table
  base := (-6098158763831737178161303713171088850833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1149551826299198733645733113804280000000000000)
      constant := (19975900417969939575173709313361818159482495047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree055.table
  base := (-6098840050806115370803949818364605091489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-413421804799549673821446053420000000000000)
      constant := (7263805937115842651171367138125134350517039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352107358396178215793/100000000000000000000)
  centralHi := (176053679198089107897/50000000000000000000)
  directionLo := (35535265610950712669/10000000000000000000)
  directionHi := (355352656109507126691/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree056.table
  base := (-1539892867304712193801884407505101953941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (112572)
      previous := (0)
      next := (64395)
      square := (566137490259112642083244603075000000000000)
      linear := (-41775683541419634468650283586410000000000000)
      constant := (739468328917733150722467183907387180279658117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree056.table
  base := (-6160167712406642369271024763621949374519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (162)
      previous := (0)
      next := (90)
      square := (806176561422730711403694700000000000000)
      linear := (-60096770550336321460582757960000000000000)
      constant := (1075557742221402074016893782014646354378367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35535265610950712669/10000000000000000000)
  centralHi := (355352656109507126691/100000000000000000000)
  directionLo := (35856858280031809199/10000000000000000000)
  directionHi := (358568582800318091991/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree057.table
  base := (-6219329362749030755061847839142814939241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1189886452020300796598682767034680000000000000)
      constant := (21447382574171916631782178036510303808947929519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree057.table
  base := (-194370358361529684785267582289363982991/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-213966491452579413313356279010000000000000)
      constant := (3899373656323745325871352965917638637335056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35856858280031809199/10000000000000000000)
  centralHi := (358568582800318091991/100000000000000000000)
  directionLo := (72351184354860566499/20000000000000000000)
  directionHi := (22609745110893927031/6250000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree058.table
  base := (-3138726795426641960678841865162582266123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-605026882440425914037578796824940000000000000)
      constant := (11101352800390097714110044183606277014308564157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree058.table
  base := (-1255582203116187862539996386513439850813/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-435188571957963403029345810320000000000000)
      constant := (8073334323143763887838868004564207236550815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72351184354860566499/20000000000000000000)
  centralHi := (22609745110893927031/6250000000000000000)
  directionLo := (182457711063497155351/50000000000000000000)
  directionHi := (364915422126994310703/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree059.table
  base := (-1266792431360257262485433425282957832129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1230221077741402859551632420265080000000000000)
      constant := (22971079811533322854668740561695062005139661555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree059.table
  base := (-6334363112153957200680660933223423993651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-442444161010767979431979062620000000000000)
      constant := (8352664406008778241404669156977052224311101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182457711063497155351/50000000000000000000)
  centralHi := (364915422126994310703/100000000000000000000)
  directionLo := (184023900399832159787/50000000000000000000)
  directionHi := (14721912031986572783/4000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree060.table
  base := (-3194435204121397808416099384462724457991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-625194195300976945514053623440140000000000000)
      constant := (11876251546982719306558393019997566142877660769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree060.table
  base := (-3194611014191528775032210686487892784869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-224849875031786277917306157460000000000000)
      constant := (4318368430979438033881706061962093253541419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184023900399832159787/50000000000000000000)
  centralHi := (14721912031986572783/4000000000000000000)
  directionLo := (371153744479045134327/100000000000000000000)
  directionHi := (46394218059880641791/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree061.table
  base := (-3221095722978531430188772968812012991643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-635277851731252461252291036747740000000000000)
      constant := (12273486822436092906560715414479185719817265837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree061.table
  base := (-644249993513491423250802673952379978067/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-228477669558188566118622783610000000000000)
      constant := (4462775547310795173601957747254166905373585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371153744479045134327/100000000000000000000)
  centralHi := (46394218059880641791/12500000000000000000)
  directionLo := (93558477838783824891/25000000000000000000)
  directionHi := (74846782271027059913/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree062.table
  base := (-3246968233517746836889323862555001041061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-645361508161527976990528450055340000000000000)
      constant := (12677244961537353146132685588220147101707322899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree062.table
  base := (-405887951590899505996274594548042692751/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-232105464084590854319939409760000000000000)
      constant := (4609553297368861351088831180607167264441608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93558477838783824891/25000000000000000000)
  centralHi := (74846782271027059913/20000000000000000000)
  directionLo := (188644466374917955133/50000000000000000000)
  directionHi := (377288932749835910267/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree063.table
  base := (-3272057526714624193590269183988518004189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (225144)
      previous := (0)
      next := (128790)
      square := (1132274980518225284166489206150000000000000)
      linear := (-93635023513114784675537980480420000000000000)
      constant := (1869646472121690027967651030362993770483631693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree063.table
  base := (-6544352785382653893549752852349045419019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (162)
      previous := (0)
      next := (90)
      square := (806176561422730711403694700000000000000)
      linear := (-67352359603140897863216010260000000000000)
      constant := (1359628989555893736825489913888556682066867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188644466374917955133/50000000000000000000)
  centralHi := (377288932749835910267/100000000000000000000)
  directionLo := (380319414627832459879/100000000000000000000)
  directionHi := (9507985365695811497/2500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree064.table
  base := (-6592735414908328485314521203516552475399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1331057642044158016934006553341080000000000000)
      constant := (27008654574758095336606759252235098200733606241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree064.table
  base := (-164823605544397418624934279851354202749/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-239361053137395430722572662060000000000000)
      constant := (4910219859173118527571407273585672881305980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380319414627832459879/100000000000000000000)
  centralHi := (9507985365695811497/2500000000000000000)
  directionLo := (76665187799992789591/20000000000000000000)
  directionHi := (95831484749990986989/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree065.table
  base := (-6639804593927742063882412224397424229709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1351224954904709048410481379956280000000000000)
      constant := (27855300848907461358143812002852914131598623531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree065.table
  base := (-6639988054232124297897247548674880945549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-485977695327595437847778576420000000000000)
      constant := (10128216649642363215537731859539930833668099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76665187799992789591/20000000000000000000)
  centralHi := (95831484749990986989/25000000000000000000)
  directionLo := (386309065228284567119/100000000000000000000)
  directionHi := (4828863315353557089/1250000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree066.table
  base := (-1337065727723810183698315702670670894747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1371392267765260079886956206571480000000000000)
      constant := (28714988599680882159049079064300810936880640865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree066.table
  base := (-3342744938507481955237608321190748178169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-246616642190200007125205914360000000000000)
      constant := (5220366723330358449205057716371653339269719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386309065228284567119/100000000000000000000)
  centralHi := (4828863315353557089/1250000000000000000)
  directionLo := (97317332810276517817/25000000000000000000)
  directionHi := (389269331241106071269/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree067.table
  base := (-52572755852129605013812543033185905843/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-347889895156452777840857758296670000000000000)
      constant := (7396929277833181005796781793731456279483636384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree067.table
  base := (-6729454495860541707539444863437358297161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-500488873433204590653045081020000000000000)
      constant := (10757989873920227923644365113756569443439111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97317332810276517817/25000000000000000000)
  centralHi := (389269331241106071269/100000000000000000000)
  directionLo := (196103627332747785891/50000000000000000000)
  directionHi := (392207254665495571783/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree068.table
  base := (-1692940350301646805554996210695785999057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-352931723371590535709976464950470000000000000)
      constant := (7618371441948281477941521641493381319303795463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree068.table
  base := (-1354377208745361370559573769146120986479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-507744462486009167055678333320000000000000)
      constant := (11079985728905956782218792007519200358312645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196103627332747785891/50000000000000000000)
  centralHi := (392207254665495571783/100000000000000000000)
  directionLo := (197561666941990442357/50000000000000000000)
  directionHi := (79024666776796176943/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree069.table
  base := (-6812678451801379886641554690188481134509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1431894206346913174316380686417080000000000000)
      constant := (31372294038210985648778399029242487268165046731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree069.table
  base := (-851598509857828417419123796295483680789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-257500025769406871729155792810000000000000)
      constant := (5703360418631854471235686763378585198565356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197561666941990442357/50000000000000000000)
  centralHi := (79024666776796176943/20000000000000000000)
  directionLo := (398018049021572356521/100000000000000000000)
  directionHi := (199009024510786178261/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree070.table
  base := (-6852067227682924874479170658374107889587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (450288)
      previous := (0)
      next := (257580)
      square := (2264549961036450568332978412300000000000000)
      linear := (-207437359886780600827550787576040000000000000)
      constant := (4612020209239807375185887852629189916567050819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree070.table
  base := (-1713040917002623975215264489880822438317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-37303974327972737132924631280000000000000)
      constant := (838442503480221590032353820991668485863562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398018049021572356521/100000000000000000000)
  centralHi := (199009024510786178261/50000000000000000000)
  directionLo := (200445931434318288513/50000000000000000000)
  directionHi := (400891862868636577027/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree071.table
  base := (-215310331298372454970123858074881763941/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-368057208017003809317332584911870000000000000)
      constant := (8302256912948819464703904260314641593035174552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree071.table
  base := (-6890015457090581507315267975805537067743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-529511229644422896263578090220000000000000)
      constant := (12074408233634048456633865287130528683680593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200445931434318288513/50000000000000000000)
  centralHi := (400891862868636577027/100000000000000000000)
  directionLo := (80749044348929022619/20000000000000000000)
  directionHi := (50468152718080639137/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree072.table
  base := (-6926271056514901550075958868569422583863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1492396144928566268745805166262680000000000000)
      constant := (34146952257781945298256378359652196106134512817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree072.table
  base := (-1385269146265562002652150092050235918209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-536766818697227472666211342520000000000000)
      constant := (12415360280020526164141397534487692200038795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80749044348929022619/20000000000000000000)
  centralHi := (50468152718080639137/12500000000000000000)
  directionLo := (406578556307363056971/100000000000000000000)
  directionHi := (101644639076840764243/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree073.table
  base := (-1740272685286765628338411095072840443861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-378140864447279325055569998219470000000000000)
      constant := (8774478746727067023369270531695439168466528099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree073.table
  base := (-1392231293292696623347915703000972992749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-544022407750032049068844594820000000000000)
      constant := (12761051091071211599771488653949761616776495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406578556307363056971/100000000000000000000)
  centralHi := (101644639076840764243/25000000000000000000)
  directionLo := (40939228231163143241/10000000000000000000)
  directionHi := (409392282311631432411/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree074.table
  base := (-874298939551361294072217898352977800549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-383182692662417082924688704873270000000000000)
      constant := (9015478895757239436320864275400875565109270182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree074.table
  base := (-349722468621352253626228605774910802571/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-275638998401418312735738923560000000000000)
      constant := (6555740291499780997520135233360293706740210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40939228231163143241/10000000000000000000)
  centralHi := (409392282311631432411/100000000000000000000)
  directionLo := (412186801321528816111/100000000000000000000)
  directionHi := (25761675082595551007/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree075.table
  base := (-7026174995800436148133522631900427998519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1552898083510219363175229646108280000000000000)
      constant := (37038953824061079568920194701658593189855846321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree075.table
  base := (-7026225930622474818446397473184736371483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-558533585855641201874111099420000000000000)
      constant := (13466648683216782381994040328438947917797333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412186801321528816111/100000000000000000000)
  centralHi := (25761675082595551007/6250000000000000000)
  directionLo := (10374062534484152371/2500000000000000000)
  directionHi := (414962501379366094841/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree076.table
  base := (-3528221289830780988908793886634379105943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-786532698185385197325852236361740000000000000)
      constant := (19014514758629814381068646205096797425478899537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree076.table
  base := (-705648742579962055372117090488505675417/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-282894587454222889138372175860000000000000)
      constant := (6913277664385065099435604269790316109522835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10374062534484152371/2500000000000000000)
  centralHi := (414962501379366094841/100000000000000000000)
  directionLo := (417719757634669881721/100000000000000000000)
  directionHi := (208859878817334940861/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree077.table
  base := (-1771298871146864605144720805578049364517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (112572)
      previous := (0)
      next := (64395)
      square := (566137490259112642083244603075000000000000)
      linear := (-56901168186832908076006403547810000000000000)
      constant := (1394005089113267927873487090784038815345502229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree077.table
  base := (-3542617486663601834096517203131130302723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-40931768854375025334241257430000000000000)
      constant := (1013657176071895578397815153025582087880939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417719757634669881721/100000000000000000000)
  centralHi := (208859878817334940861/50000000000000000000)
  directionLo := (16818357317441642973/4000000000000000000)
  directionHi := (210229466468020537163/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree078.table
  base := (-3556217384310189916687411070486680350039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-806700011045936228802327062976940000000000000)
      constant := (20024146306083352645967628895957062829940282001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree078.table
  base := (-56899756340447513914571634721015873667/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-580300353014054931082010856320000000000000)
      constant := (14560584044427821039293137284993777773789625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16818357317441642973/4000000000000000000)
  centralHi := (210229466468020537163/50000000000000000000)
  directionLo := (211590189194266060901/50000000000000000000)
  directionHi := (423180378388532121803/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree079.table
  base := (-7138161352880423855502250112447921356651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1633567334952423489081128952569080000000000000)
      constant := (41077479741461347337399693037160075656549199709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree079.table
  base := (-3569095988426461897549797418267511034649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-293777971033429753742322054310000000000000)
      constant := (7467353012854495647085359462557391959302199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211590189194266060901/50000000000000000000)
  centralHi := (423180378388532121803/100000000000000000000)
  directionLo := (85176886775793387943/20000000000000000000)
  directionHi := (106471108469741734929/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree080.table
  base := (-111912125627289292735598399931674858433/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-413433661953243630139400944796070000000000000)
      constant := (10529925943140033551103963581049669452966775152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree080.table
  base := (-7162403010798563736822774270902437983037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-594811531119664083887277360920000000000000)
      constant := (15313566372855608948538686462325780538831187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85176886775793387943/20000000000000000000)
  centralHi := (106471108469741734929/25000000000000000000)
  directionLo := (107142857142857142857/25000000000000000000)
  directionHi := (428571428571428571429/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree081.table
  base := (-7185079530834439567459198071774489063401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1673901960673525552034078605799480000000000000)
      constant := (43174964609057136541391814320435367550824422959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree081.table
  base := (-7185103284961921056685124673195644894857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-602067120172468660289910613220000000000000)
      constant := (15697165054479789964779527427158413400152007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107142857142857142857/25000000000000000000)
  centralHi := (428571428571428571429/100000000000000000000)
  directionLo := (8624833627499188829/2000000000000000000)
  directionHi := (431241681374959441451/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree082.table
  base := (-3603136218374635349351432224098048410669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-847034636767038291755276716207340000000000000)
      constant := (22121631083371446192771907917697800518707108171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree082.table
  base := (-7206293358607010768067847985287454478599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-609322709225273236692543865520000000000000)
      constant := (16085502043177597607237562924460914730548649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8624833627499188829/2000000000000000000)
  centralHi := (431241681374959441451/100000000000000000000)
  directionLo := (433895501385355434283/100000000000000000000)
  directionHi := (108473875346338858571/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree083.table
  base := (-1806488823233166660681260265730484243683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-428559146598656903746757064757470000000000000)
      constant := (11331149092993433204339495475662150418215228197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree083.table
  base := (-7225973720629291532098590141203287450319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-616578298278077813095177117820000000000000)
      constant := (16478577314993154401517538303466038914934369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433895501385355434283/100000000000000000000)
  centralHi := (108473875346338858571/25000000000000000000)
  directionLo := (218266594151393170979/50000000000000000000)
  directionHi := (436533188302786341959/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree084.table
  base := (-7244128567877621729047387088182782848037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (450288)
      previous := (0)
      next := (257580)
      square := (2264549961036450568332978412300000000000000)
      linear := (-247771985607882663780500440806440000000000000)
      constant := (6631281022895116229189231690295621940859048469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree084.table
  base := (-3622072399488343855764089669527019215317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-44559563380777313535557883580000000000000)
      constant := (1205456489211215146703190213033310865492781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218266594151393170979/50000000000000000000)
  centralHi := (436533188302786341959/100000000000000000000)
  directionLo := (439155032826839930709/100000000000000000000)
  directionHi := (43915503282683993071/10000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree085.table
  base := (-7260792672342774579699432636414026064421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1754571212115729677939977912260280000000000000)
      constant := (47526374475081904967868969069452137038467029139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree085.table
  base := (-3630403484385796092490573744582719176473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-315544738191843482950221811210000000000000)
      constant := (8639471313344086656583167448927946760352823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439155032826839930709/100000000000000000000)
  centralHi := (43915503282683993071/10000000000000000000)
  directionLo := (220880658515231815169/50000000000000000000)
  directionHi := (441761317030463630339/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree086.table
  base := (-7275947966964177458517883082319163904189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1774738524976280709416452738875480000000000000)
      constant := (48646818266783700038344275650317387961063521851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree086.table
  base := (-727596055931828343372082843719706271043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-319172532718245771151538437360000000000000)
      constant := (8843116316025364266950325345598671963594465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220880658515231815169/50000000000000000000)
  centralHi := (441761317030463630339/100000000000000000000)
  directionLo := (444352314714165447311/100000000000000000000)
  directionHi := (27772019669635340457/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree087.table
  base := (-3644797384416733134702217975093958329407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-897452918918415870446463782745340000000000000)
      constant := (24890149245863194479150804012862172481582091113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree087.table
  base := (-3644802930076549656184504534326769869823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-322800327244648059352855063510000000000000)
      constant := (9049130425428698580585571402550488276378673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444352314714165447311/100000000000000000000)
  centralHi := (27772019669635340457/6250000000000000000)
  directionLo := (446928291741733075831/100000000000000000000)
  directionHi := (55866036467716634479/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree088.table
  base := (-7301733357186816497432085920584197636483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1815073150697382772369402392105880000000000000)
      constant := (50926815111475625297800034134845510453116843397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree088.table
  base := (-7301743126271754385777724245878560570821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-652856243542100695108343379320000000000000)
      constant := (18515027270613389181300061531311950532029771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446928291741733075831/100000000000000000000)
  centralHi := (55866036467716634479/12500000000000000000)
  directionLo := (224744753179318188641/50000000000000000000)
  directionHi := (449489506358636377283/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree089.table
  base := (-7312363978328224863616427041098431572369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1835240463557933803845877218721080000000000000)
      constant := (52086368092129880644162246597376490779947558471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree089.table
  base := (-3656186291324355078126350775810272923289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-330055916297452635755488315810000000000000)
      constant := (9468265940147477990337213109137796626758839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224744753179318188641/50000000000000000000)
  centralHi := (449489506358636377283/100000000000000000000)
  directionLo := (113009052373548141963/25000000000000000000)
  directionHi := (452036209494192567853/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree090.table
  base := (-7321486849892936333639729463253481219553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1855407776418484835322352045336280000000000000)
      constant := (53258957403733622245066772067391527591459505527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree090.table
  base := (-1464298885629391830016209963348208369613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-667367421647709847913609883920000000000000)
      constant := (19362774670157810925506168533279688949444815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113009052373548141963/25000000000000000000)
  centralHi := (452036209494192567853/100000000000000000000)
  directionLo := (227284322524247418557/50000000000000000000)
  directionHi := (90913729009698967423/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree091.table
  base := (-229034442641929793139740299432250279753/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (112572)
      previous := (0)
      next := (64395)
      square := (566137490259112642083244603075000000000000)
      linear := (-66984824617108423814243816855410000000000000)
      constant := (1944449393563172306690413877264869301993734088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree091.table
  base := (-3664554419451253033309284783788457579511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-48187357907179601736874509730000000000000)
      constant := (1413839687969377841823346732180980796943423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227284322524247418557/50000000000000000000)
  centralHi := (90913729009698967423/20000000000000000000)
  directionLo := (228543525082516518759/50000000000000000000)
  directionHi := (457087050165033037519/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree092.table
  base := (-1833802523291027596328295877769044027283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-473935600534896724568825424641670000000000000)
      constant := (13910811229178523758323456574052631011040740597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree092.table
  base := (-916901996406979773388629381298773837533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-340939299876659500359438194260000000000000)
      constant := (10114737378437354341977769215985440327843532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228543525082516518759/50000000000000000000)
  centralHi := (457087050165033037519/100000000000000000000)
  directionLo := (459591655489868927349/100000000000000000000)
  directionHi := (9191833109797378547/2000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree093.table
  base := (-7339810787656828056014543265211939615909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1915909715000137929751776525181880000000000000)
      constant := (56854943073662203283904257717004003419326669331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree093.table
  base := (-7339815964292451281059780417404044543539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-689134188806123577121509640820000000000000)
      constant := (20669932039252878328086361704132201817366589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459591655489868927349/100000000000000000000)
  centralHi := (9191833109797378547/2000000000000000000)
  directionLo := (462082685418167671601/100000000000000000000)
  directionHi := (231041342709083835801/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree094.table
  base := (-146858087666721858569193002023631234983/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-968038513930344480614125675898540000000000000)
      constant := (29039838735994047054088644762854994329642622425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree094.table
  base := (-7342908942045766290313548863385138185807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-696389777858928153524142893120000000000000)
      constant := (21115127472628161091769029650474128228895457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462082685418167671601/100000000000000000000)
  centralHi := (231041342709083835801/50000000000000000000)
  directionLo := (464560358328831416121/100000000000000000000)
  directionHi := (232280179164415708061/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree095.table
  base := (-7344491001032193331791583387015064212357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1956244340721239992704726178412280000000000000)
      constant := (59317448095060565790201339135033459546746970163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree095.table
  base := (-1836123753852077276725102833887275346251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-351822683455866364963388072710000000000000)
      constant := (10782530525783411603147034397291547016067402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464560358328831416121/100000000000000000000)
  centralHi := (232280179164415708061/50000000000000000000)
  directionLo := (29189055425495581823/6250000000000000000)
  directionHi := (467024886807929309169/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree096.table
  base := (-7344570748909681770764733696416020542271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-1976411653581791024181201005027480000000000000)
      constant := (60568254927991741158669507472019282516541277289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree096.table
  base := (-918071785473829960218376434312018856719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-355450477982268653164704698860000000000000)
      constant := (11009866385598873617033036799034844304083076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29189055425495581823/6250000000000000000)
  centralHi := (467024886807929309169/100000000000000000000)
  directionLo := (469476477861570954391/100000000000000000000)
  directionHi := (58684559732696369299/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree097.table
  base := (-1835785931012438139060617679650503544157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-499144741610585513914418957910670000000000000)
      constant := (15458024489354816886860062367318465041678686363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree097.table
  base := (-734314683656204638764188967994440564173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-359078272508670941366021325010000000000000)
      constant := (11239571313570919022409202790673862061777615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469476477861570954391/100000000000000000000)
  centralHi := (58684559732696369299/12500000000000000000)
  directionLo := (471915333118826582193/100000000000000000000)
  directionHi := (235957666559413291097/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree098.table
  base := (-7340210013826577463604866927358763498441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (450288)
      previous := (0)
      next := (257580)
      square := (2264549961036450568332978412300000000000000)
      linear := (-288106611328984726733450094036840000000000000)
      constant := (9015568167330982368454068081633264633330154617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree098.table
  base := (-7340212754302330979927401865235736099477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (162)
      previous := (0)
      next := (90)
      square := (806176561422730711403694700000000000000)
      linear := (-103630304867163779876382271760000000000000)
      constant := (3277612945064383621791327043523349847303661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471915333118826582193/100000000000000000000)
  centralHi := (235957666559413291097/50000000000000000000)
  directionLo := (474341649025256899799/100000000000000000000)
  directionHi := (2371708245126284499/500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree099.table
  base := (-1833942424276252094610699090323931527661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-509228398040861029652656371218270000000000000)
      constant := (16099723139707382793874893821237003740601212299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree099.table
  base := (-7335772109889983639554528765307251807761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-732667723122951035537309154620000000000000)
      constant := (23412176732553243138362126712004944661419711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474341649025256899799/100000000000000000000)
  centralHi := (2371708245126284499/500000000000000000)
  directionLo := (476755617027578332417/100000000000000000000)
  directionHi := (238377808513789166209/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree100.table
  base := (-7329822845283330256746467989020235219091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-2057080905023995150087100311488280000000000000)
      constant := (65701844110129899996776097257171265804209095669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree100.table
  base := (-1465964993889717813698639030876918920907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-739923312175755611939942406920000000000000)
      constant := (23885800975209455751890391489435154864377785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476755617027578332417/100000000000000000000)
  centralHi := (238377808513789166209/50000000000000000000)
  directionLo := (14973669492186091717/3125000000000000000)
  directionHi := (95831484749990986989/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree101.table
  base := (-732236952320154204122171924356869998333/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-1038624108942273090781787569051740000000000000)
      constant := (33508915908146670374267534158991020282797237735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree101.table
  base := (-7322371393170330878923463399263747355799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-747178901228560188342575659220000000000000)
      constant := (24364163340469906196127260580981076379565849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14973669492186091717/3125000000000000000)
  centralHi := (95831484749990986989/20000000000000000000)
  directionLo := (240773625581188198549/50000000000000000000)
  directionHi := (481547251162376397099/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree102.table
  base := (-3656704894966441248003726824335723941973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-1048707765372548606520024982359340000000000000)
      constant := (34173427834594476887020822823735286620902894307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree102.table
  base := (-7313411436032902487040553556581170275627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-754434490281364764745208911520000000000000)
      constant := (24847263825640687493679168203867522656494277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240773625581188198549/50000000000000000000)
  centralHi := (481547251162376397099/100000000000000000000)
  directionLo := (30245329796347004263/6250000000000000000)
  directionHi := (483925276741552068209/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree103.table
  base := (-7302943699473938521543882641815405919337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-2117582843605648244516524791333880000000000000)
      constant := (69688915661384594855732338103169725713856535983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree103.table
  base := (-456434071776495550651291475453291845633/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-380845039667084670573921081910000000000000)
      constant := (12667551214126403011792440328514809596511864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30245329796347004263/6250000000000000000)
  centralHi := (483925276741552068209/100000000000000000000)
  directionLo := (24314583681236179757/5000000000000000000)
  directionHi := (486291673624723595141/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree104.table
  base := (-911371412668327641021078662191745436229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-534437539116549818998249904487270000000000000)
      constant := (17761002946516004660058316226869411932824008422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree104.table
  base := (-911371572085637945520876060197993512309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-384472834193486958775237708060000000000000)
      constant := (12913839573017759396902170204441193271587436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree104.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24314583681236179757/5000000000000000000)
  centralHi := (486291673624723595141/100000000000000000000)
  directionLo := (488646610756773419629/100000000000000000000)
  directionHi := (48864661075677341963/10000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree105.table
  base := (-7277492641123522622125607712772327716653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (450288)
      previous := (0)
      next := (257580)
      square := (2264549961036450568332978412300000000000000)
      linear := (-308273924189535758209924920652040000000000000)
      constant := (10344592005279223992845815354310957720107452061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree105.table
  base := (-7277493763586608640331100041437159140321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (162)
      previous := (0)
      next := (90)
      square := (806176561422730711403694700000000000000)
      linear := (-110885893919968356279015524060000000000000)
      constant := (3760713425270440984518146196884939886017753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree105.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488646610756773419629/100000000000000000000)
  centralHi := (48864661075677341963/10000000000000000000)
  directionLo := (61373781628872857231/12500000000000000000)
  directionHi := (490990253030982857849/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree106.table
  base := (-7262507760886638206396496575393127826773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25970000000000000000000000000000000000000000
      center := (59472)
      previous := (0)
      next := (34020)
      square := (299091504287833093930770733700000000000000)
      linear := (-41095939286552855451810363607160000000000000)
      constant := (1392326649212528960057755935565864047033870519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree106.table
  base := (-1815627187185242016407833782285685752059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-391728423246291535177870960360000000000000)
      constant := (13413523459442248319871864059846002796298218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree106.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61373781628872857231/12500000000000000000)
  centralHi := (490990253030982857849/100000000000000000000)
  directionLo := (493322761423771638041/100000000000000000000)
  directionHi := (246661380711885819021/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree107.table
  base := (-7246016699628112379302331857735898452589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-2198252095047852370422424097794680000000000000)
      constant := (75187516894625501678760930509651133201087197451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree107.table
  base := (-36230087844821339342639877514873265431/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-395356217772693823379187586510000000000000)
      constant := (13666918985102879911379950903609620999388100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree107.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493322761423771638041/100000000000000000000)
  centralHi := (246661380711885819021/50000000000000000000)
  directionLo := (495644293123730467289/100000000000000000000)
  directionHi := (49564429312373046729/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree108.table
  base := (-903502436700065794903248663503817819909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-554604851977100850474724731102470000000000000)
      constant := (19148689372762281701385216963323902022899810662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree108.table
  base := (-7228020258591617914720713791375093717017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-797968024598192223161008425320000000000000)
      constant := (27845367129174456057256259501982620407866167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree108.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495644293123730467289/100000000000000000000)
  centralHi := (49564429312373046729/10000000000000000000)
  directionLo := (31122187603452457113/6250000000000000000)
  directionHi := (497955001655239313809/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree109.table
  base := (-1802129044155813137655956965588988822223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (788004)
      previous := (0)
      next := (450765)
      square := (3962962431813788494582712221525000000000000)
      linear := (-559646680192238608343843437756270000000000000)
      constant := (19503758548219994506569774728900845989520404057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree109.table
  base := (-3604258424876409666619162933955181372417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-402611806825498399781820838810000000000000)
      constant := (14180817197108112543955195593088696112751567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree109.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31122187603452457113/6250000000000000000)
  centralHi := (497955001655239313809/100000000000000000000)
  directionLo := (500255036996946515033/100000000000000000000)
  directionHi := (250127518498473257517/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree110.table
  base := (-3593753390175272298870142384686681775269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1576008)
      previous := (0)
      next := (901530)
      square := (7925924863627576989165424443050000000000000)
      linear := (-1129377016814752732425924288820140000000000000)
      constant := (39724173497880566107564087554615740433770199571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree110.table
  base := (-7187507372613411795042254844531644421667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-812479202703801375966274929920000000000000)
      constant := (28882639763852955470845186147317949423338317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree110.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500255036996946515033/100000000000000000000)
  centralHi := (250127518498473257517/50000000000000000000)
  directionLo := (251272272847683726137/50000000000000000000)
  directionHi := (20101781827814698091/4000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree111.table
  base := (-7164991334506288656162753112022914820371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-2278921346490056496328323404255480000000000000)
      constant := (80894695895601363957746892062850933981209315189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree111.table
  base := (-3582495927792795836946935948466689307519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (567)
      previous := (0)
      next := (315)
      square := (2821617964979557489912931450000000000000)
      linear := (-409867395878302976184454091110000000000000)
      constant := (14704191618346224791873168598897632223931569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree111.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251272272847683726137/50000000000000000000)
  centralHi := (20101781827814698091/4000000000000000000)
  directionLo := (504823670973846276991/100000000000000000000)
  directionHi := (3943934929483174039/781250000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree112.table
  base := (-3570484933544848760221730631893679993201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (225144)
      previous := (0)
      next := (128790)
      square := (1132274980518225284166489206150000000000000)
      linear := (-164220618525043394843199873633620000000000000)
      constant := (5882434349181916686134306179350514570293688737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree112.table
  base := (-446310645344556278946039189088634630599/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (81)
      previous := (0)
      next := (45)
      square := (403088280711365355701847350000000000000)
      linear := (-59070741486386466340824388180000000000000)
      constant := (2138490343672812420960001091971036460686456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree112.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504823670973846276991/100000000000000000000)
  centralHi := (3943934929483174039/781250000000000000)
  directionLo := (101418510567421989301/20000000000000000000)
  directionHi := (253546276418554973253/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree113.table
  base := (-284617696182226829617436620496862195969/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-2319255972211158559281273057485880000000000000)
      constant := (83826501970956262330586971994447424762115771775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree113.table
  base := (-7115442807832070236530207736109554348447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-834245969862215105174174686820000000000000)
      constant := (30474084486787328528311995728915631836926097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree113.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101418510567421989301/20000000000000000000)
  centralHi := (253546276418554973253/50000000000000000000)
  directionLo := (254675664085815275229/50000000000000000000)
  directionHi := (509351328171630550459/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree114.table
  base := (-7088408971973059274552872576268852753839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3152016)
      previous := (0)
      next := (1803060)
      square := (15851849727255153978330848886100000000000000)
      linear := (-2339423285071709590757747884101080000000000000)
      constant := (85311959139379148417100058266002098838108846201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree114.table
  base := (-7088409326714968670295999356836591198841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1134)
      previous := (0)
      next := (630)
      square := (5643235929959114979825862900000000000000)
      linear := (-841501558915019681576807939120000000000000)
      constant := (31014042261611891972227430640695007031256791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree114.checked
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
end ForestUnimodality.Stage170KernelData.Cell319.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell319
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 114 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 114 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 114 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel114.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell319

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell319.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 114 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell319.Kernel349

