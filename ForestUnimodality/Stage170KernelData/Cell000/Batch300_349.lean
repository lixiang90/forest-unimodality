import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell000.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch300_349
import ForestUnimodality.BinomialMassData.Q9_35.Batch300_349

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel300
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475870618383426693333/100000000000000000000)
  centralHi := (237935309191713346667/50000000000000000000)
  directionLo := (95333678061415935797/20000000000000000000)
  directionHi := (238334195153539839493/50000000000000000000)

def endpointA : IntegerEndpointWitness 300 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree300.table
  base := (5819590844046047357072540706841177725839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-71291053207775783029376273280000000000000)
      constant := (2673541241179212235820054758827364710903356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 300 interval.damping) (curvature.centralUpper 300 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree300.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 300 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree300.table
  base := (2909795422023023354424682915644275302081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4492416760906007308987164680400000000000000)
      constant := (173246180061386328591809884796665694898019690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 300 interval.damping) (curvature.centralUpper 300 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree300.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 300 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel301
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95333678061415935797/20000000000000000000)
  centralHi := (238334195153539839493/50000000000000000000)
  directionLo := (95492965855137201461/20000000000000000000)
  directionHi := (238732414637843003653/50000000000000000000)

def endpointA : IntegerEndpointWitness 301 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree301.table
  base := (5978369350453093834552382306958471233181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-71530747973356241312115069360000000000000)
      constant := (2692029080352481924772660543057833884932724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 301 interval.damping) (curvature.centralUpper 301 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree301.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 301 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree301.table
  base := (5978369350453093266396873977779205609537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-643931075876796597257101261920000000000000)
      constant := (24920316457776155308768803187966272196333795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 301 interval.damping) (curvature.centralUpper 301 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree301.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 301 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel302
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/20000000000000000000)
  centralHi := (238732414637843003653/50000000000000000000)
  directionLo := (478259941948494698549/100000000000000000000)
  directionHi := (9565198838969893971/2000000000000000000)

def endpointA : IntegerEndpointWitness 302 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree302.table
  base := (6138033604813943071594604308775829986129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-71770442738936699594853865440000000000000)
      constant := (2710580386208961939334200547915103319944516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 302 interval.damping) (curvature.centralUpper 302 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree302.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 302 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree302.table
  base := (1534508401203485643405440597695586961279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4522618301369145052612252986480000000000000)
      constant := (175642350410930930828804686496653675222053420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 302 interval.damping) (curvature.centralUpper 302 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree302.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 302 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel303
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478259941948494698549/100000000000000000000)
  centralHi := (9565198838969893971/2000000000000000000)
  directionLo := (479053734929491028093/100000000000000000000)
  directionHi := (239526867464745514047/50000000000000000000)

def endpointA : IntegerEndpointWitness 303 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree303.table
  base := (787322950094838482435309554870641943227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-72010137504517157877592661520000000000000)
      constant := (2729195158723172730669807852305860542183264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 303 interval.damping) (curvature.centralUpper 303 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree303.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 303 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree303.table
  base := (98415368761854803484797697170267767663/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4537719071600713924424797139520000000000000)
      constant := (176846585679319237228242317618741798596955840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 303 interval.damping) (curvature.centralUpper 303 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree303.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 303 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel304
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479053734929491028093/100000000000000000000)
  centralHi := (239526867464745514047/50000000000000000000)
  directionLo := (47984621476803647451/10000000000000000000)
  directionHi := (479846214768036474511/100000000000000000000)

def endpointA : IntegerEndpointWitness 304 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree304.table
  base := (6460019331969052551276637820786530542967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-72249832270097616160331457600000000000000)
      constant := (2747873397869840956191725012723146122171868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 304 interval.damping) (curvature.centralUpper 304 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree304.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 304 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree304.table
  base := (1292003866393810433748541493784704117153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4552819841832282796237341292560000000000000)
      constant := (178054921008050014126456356569694262543512425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 304 interval.damping) (curvature.centralUpper 304 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree304.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 304 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel305
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47984621476803647451/10000000000000000000)
  centralHi := (479846214768036474511/100000000000000000000)
  directionLo := (240318693979749585611/50000000000000000000)
  directionHi := (480637387959499171223/100000000000000000000)

def endpointA : IntegerEndpointWitness 305 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree305.table
  base := (6622340792177611247790231676288633590823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-72489527035678074443070253680000000000000)
      constant := (2766615103623897152303204602055154534363292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 305 interval.damping) (curvature.centralUpper 305 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree305.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 305 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree305.table
  base := (3311170396088805456259653415864862853649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4567920612063851668049885445600000000000000)
      constant := (179267356395587756878375695422773782798288010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 305 interval.damping) (curvature.centralUpper 305 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree305.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 305 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel306
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240318693979749585611/50000000000000000000)
  centralHi := (480637387959499171223/100000000000000000000)
  directionLo := (240713630472937516709/50000000000000000000)
  directionHi := (481427260945875033419/100000000000000000000)

def endpointA : IntegerEndpointWitness 306 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree306.table
  base := (6785547975167414393024176473088593547939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-72729221801258532725809049760000000000000)
      constant := (2785420275960473440780250294172354374191756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 306 interval.damping) (curvature.centralUpper 306 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree306.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 306 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree306.table
  base := (3392773987583707049589788024282594400431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4583021382295420539862429598640000000000000)
      constant := (180483891840409307942981901886586471256211190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 306 interval.damping) (curvature.centralUpper 306 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree306.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 306 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel307
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240713630472937516709/50000000000000000000)
  centralHi := (481427260945875033419/100000000000000000000)
  directionLo := (48221584011639972823/10000000000000000000)
  directionHi := (482215840116399728231/100000000000000000000)

def endpointA : IntegerEndpointWitness 307 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree307.table
  base := (6949640874771323631063695403833427180817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-72968916566838991008547845840000000000000)
      constant := (2804288914854901268199202981845333708723268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 307 interval.damping) (curvature.centralUpper 307 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree307.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 307 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree307.table
  base := (277985634990852934941166794256391646063/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4598122152526989411674973751680000000000000)
      constant := (181704527341003718423252361371692398832135875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 307 interval.damping) (curvature.centralUpper 307 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree307.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 307 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel308
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48221584011639972823/10000000000000000000)
  centralHi := (482215840116399728231/100000000000000000000)
  directionLo := (483003131808151652639/100000000000000000000)
  directionHi := (3018769573800947829/625000000000000000)

def endpointA : IntegerEndpointWitness 308 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree308.table
  base := (7114619484871474779549595146605282995457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-73208611332419449291286641920000000000000)
      constant := (2823221020282709177830625891786421131981828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 308 interval.damping) (curvature.centralUpper 308 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree308.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 308 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree308.table
  base := (1422923896974294910768089884996477238521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-659031846108365469069645414960000000000000)
      constant := (26132751842267444513523400337810383516741175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 308 interval.damping) (curvature.centralUpper 308 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree308.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 308 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel309
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483003131808151652639/100000000000000000000)
  centralHi := (3018769573800947829/625000000000000000)
  directionLo := (24189457115332304003/5000000000000000000)
  directionHi := (483789142306646080061/100000000000000000000)

def endpointA : IntegerEndpointWitness 309 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree309.table
  base := (7280483799398728777784783342275179617829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-73448306097999907574025438000000000000000)
      constant := (2842216592219620613431730654559100718471316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 309 interval.damping) (curvature.centralUpper 309 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree309.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 309 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree309.table
  base := (7280483799398728579969958151208571602289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4628323692990127155300062057760000000000000)
      constant := (184158098503527548387481077997774100042560805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 309 interval.damping) (curvature.centralUpper 309 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree309.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 309 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel310
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24189457115332304003/5000000000000000000)
  centralHi := (483789142306646080061/100000000000000000000)
  directionLo := (242286938923210316599/50000000000000000000)
  directionHi := (484573877846420633199/100000000000000000000)

def endpointA : IntegerEndpointWitness 310 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree310.table
  base := (1861808453083032617623995038452802545643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-73688000863580365856764234080000000000000)
      constant := (2861275630641551754381424150815244840730288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 310 interval.damping) (curvature.centralUpper 310 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree310.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 310 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree310.table
  base := (3723616906166065148564870600360814283803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4643424463221696027112606210800000000000000)
      constant := (185391034162494894788781139336576798999063470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 310 interval.damping) (curvature.centralUpper 310 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree310.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 310 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel311
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242286938923210316599/50000000000000000000)
  centralHi := (484573877846420633199/100000000000000000000)
  directionLo := (485357344611612237427/100000000000000000000)
  directionHi := (121339336152903059357/25000000000000000000)

def endpointA : IntegerEndpointWitness 311 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree311.table
  base := (951858689712296886386739348558408465221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-73927695629160824139503030160000000000000)
      constant := (2880398135524609381613349297383869070887072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 311 interval.damping) (curvature.centralUpper 311 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree311.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 311 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree311.table
  base := (475929344856148433697247872991685349039/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4658525233453264898925150363840000000000000)
      constant := (186628069871310691130853847392695406568232880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 311 interval.damping) (curvature.centralUpper 311 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree311.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 311 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel312
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485357344611612237427/100000000000000000000)
  centralHi := (121339336152903059357/25000000000000000000)
  directionLo := (486139548736525705731/100000000000000000000)
  directionHi := (121534887184131426433/25000000000000000000)

def endpointA : IntegerEndpointWitness 312 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree312.table
  base := (1945847727392820577769882628561130447561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-74167390394741282422241826240000000000000)
      constant := (2899584106845088773813509867336978087160976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 312 interval.damping) (curvature.centralUpper 312 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree312.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 312 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree312.table
  base := (3891695454785641088961256405713471483929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4673626003684833770737694516880000000000000)
      constant := (187869205628523023233308302854031601027125210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 312 interval.damping) (curvature.centralUpper 312 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree312.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 312 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel313
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486139548736525705731/100000000000000000000)
  centralHi := (121534887184131426433/25000000000000000000)
  directionLo := (19476819852247764123/4000000000000000000)
  directionHi := (121730124076548525769/25000000000000000000)

def endpointA : IntegerEndpointWitness 313 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree313.table
  base := (3976398991035638862472836596832362044687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-74407085160321740704980622320000000000000)
      constant := (2918833544579471633359877244124658896357496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 313 interval.damping) (curvature.centralUpper 313 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree313.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 313 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree313.table
  base := (3976398991035638804124569483475877155639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4688726773916402642550238669920000000000000)
      constant := (189114441432691395366875346243295179806263110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 313 interval.damping) (curvature.centralUpper 313 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree313.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 313 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel314
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19476819852247764123/4000000000000000000)
  centralHi := (121730124076548525769/25000000000000000000)
  directionLo := (243850096678465517511/50000000000000000000)
  directionHi := (487700193356931035023/100000000000000000000)

def endpointA : IntegerEndpointWitness 314 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree314.table
  base := (2030772682341220410651580154086607070903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-74646779925902198987719418400000000000000)
      constant := (2938146448704424041492107338905385713134448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 314 interval.damping) (curvature.centralUpper 314 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree314.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 314 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree314.table
  base := (4061545364682440770168192527260554958039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4703827544147971514362782822960000000000000)
      constant := (190363777282386605007554110012405671929439110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 314 interval.damping) (curvature.centralUpper 314 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree314.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 314 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel315
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243850096678465517511/50000000000000000000)
  centralHi := (487700193356931035023/100000000000000000000)
  directionLo := (244239322938437501183/50000000000000000000)
  directionHi := (488478645876875002367/100000000000000000000)

def endpointA : IntegerEndpointWitness 315 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree315.table
  base := (8294269145664205063936490543874540975247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-74886474691482657270458214480000000000000)
      constant := (2957522819196794442209700222725498163900988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 315 interval.damping) (curvature.centralUpper 315 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree315.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 315 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree315.table
  base := (4147134572832102487155230214206267569587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-674132616339934340882189568000000000000000)
      constant := (27373887596598659907196502207594438729871090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 315 interval.damping) (curvature.centralUpper 315 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree315.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 315 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel316
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244239322938437501183/50000000000000000000)
  centralHi := (488478645876875002367/100000000000000000000)
  directionLo := (489255859806525960667/100000000000000000000)
  directionHi := (122313964951631490167/25000000000000000000)

def endpointA : IntegerEndpointWitness 316 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree316.table
  base := (8466333225226452712589265090068163961273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-75126169457063115553197010560000000000000)
      constant := (2976962656033611654407268224040272655845092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 316 interval.damping) (curvature.centralUpper 316 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree316.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 316 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree316.table
  base := (8466333225226452634044631218599537595661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4734029084611109257987871129040000000000000)
      constant := (192874749112696453552688512767404886710936945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 316 interval.damping) (curvature.centralUpper 316 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree316.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 316 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel317
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489255859806525960667/100000000000000000000)
  centralHi := (122313964951631490167/25000000000000000000)
  directionLo := (490031841039274220671/100000000000000000000)
  directionHi := (3828373758119329849/781250000000000000)

def endpointA : IntegerEndpointWitness 317 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree317.table
  base := (2159820740588358252172443831083845539057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-75365864222643573835935806640000000000000)
      constant := (2996465959192082911765311867127341528624912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 317 interval.damping) (curvature.centralUpper 317 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree317.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 317 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree317.table
  base := (8639282962353432939857030561846024846291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4749129854842678129800415282080000000000000)
      constant := (194136385090508050677471044573644276087341295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 317 interval.damping) (curvature.centralUpper 317 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree317.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 317 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel318
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490031841039274220671/100000000000000000000)
  centralHi := (3828373758119329849/781250000000000000)
  directionLo := (490806595421921822819/100000000000000000000)
  directionHi := (24540329771096091141/5000000000000000000)

def endpointA : IntegerEndpointWitness 318 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree318.table
  base := (8813118351391074862439670353553394792913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-75605558988224032118674602720000000000000)
      constant := (3016032728649591929924637748414213579171652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 318 interval.damping) (curvature.centralUpper 318 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree318.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 318 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree318.table
  base := (8813118351391074802118481577486451951837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4764230625074247001612959435120000000000000)
      constant := (195402121108240163307763962536116180728200065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 318 interval.damping) (curvature.centralUpper 318 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree318.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 318 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel319
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490806595421921822819/100000000000000000000)
  centralHi := (24540329771096091141/5000000000000000000)
  directionLo := (245790064377598258163/50000000000000000000)
  directionHi := (491580128755196516327/100000000000000000000)

def endpointA : IntegerEndpointWitness 319 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree319.table
  base := (8987839386728951173033150058291150454699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-75845253753804490401413398800000000000000)
      constant := (3035662964383697000482022667423164601818796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 319 interval.damping) (curvature.centralUpper 319 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree319.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 319 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree319.table
  base := (4493919693364475560085735199314758685181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4779331395305815873425503588160000000000000)
      constant := (196671957164518236803906175757432231755738690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 319 interval.damping) (curvature.centralUpper 319 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree319.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 319 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel320
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245790064377598258163/50000000000000000000)
  centralHi := (491580128755196516327/100000000000000000000)
  directionLo := (98470489358851694127/20000000000000000000)
  directionHi := (123088111698564617659/25000000000000000000)

def endpointA : IntegerEndpointWitness 320 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree320.table
  base := (4581723031399904459790553137195234551471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-76084948519384948684152194880000000000000)
      constant := (3055356666372129111353910191497561876411768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 320 interval.damping) (curvature.centralUpper 320 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree320.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 320 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree320.table
  base := (916344606279980887325686502480387523983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4794432165537384745238047741200000000000000)
      constant := (197945893257978294175811696897476949433758350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 320 interval.damping) (curvature.centralUpper 320 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree320.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 320 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel321
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98470489358851694127/20000000000000000000)
  centralHi := (123088111698564617659/25000000000000000000)
  directionLo := (9862471104983996889/2000000000000000000)
  directionHi := (493123555249199844451/100000000000000000000)

def endpointA : IntegerEndpointWitness 321 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree321.table
  base := (4669969187039552866497591620744273221679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-76324643284965406966890990960000000000000)
      constant := (3075113834592790093063946897595954185773432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 321 interval.damping) (curvature.centralUpper 321 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree321.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 321 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree321.table
  base := (933993837407910569240023551395252595923/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4809532935768953617050591894240000000000000)
      constant := (199223929387266822543081790620446368860011350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 321 interval.damping) (curvature.centralUpper 321 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree321.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 321 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel322
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9862471104983996889/2000000000000000000)
  centralHi := (493123555249199844451/100000000000000000000)
  directionLo := (493893459785537335019/100000000000000000000)
  directionHi := (24694672989276866751/5000000000000000000)

def endpointA : IntegerEndpointWitness 322 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree322.table
  base := (9517316315084552839994526365195568280421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-76564338050545865249629787040000000000000)
      constant := (3094934469023750790519009367340782273121684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 322 interval.damping) (curvature.centralUpper 322 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree322.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 322 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree322.table
  base := (190346326301691056088411675019741635111/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-689233386571503212694733721040000000000000)
      constant := (28643723650148665879469587484020547861444250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 322 interval.damping) (curvature.centralUpper 322 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree322.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 322 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel323
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493893459785537335019/100000000000000000000)
  centralHi := (24694672989276866751/5000000000000000000)
  directionLo := (98932433204939565569/20000000000000000000)
  directionHi := (247331083012348913923/50000000000000000000)

def endpointA : IntegerEndpointWitness 323 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree323.table
  base := (1211947485046958034067363256389906422439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-76804032816126323532368583120000000000000)
      constant := (3114818569643249259846936682354477005518048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 323 interval.damping) (curvature.centralUpper 323 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree323.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 323 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree323.table
  base := (4847789940187832120682601956775680087433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4839734476232091360675680200320000000000000)
      constant := (201792301747966890953279249274092083242842170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 323 interval.damping) (curvature.centralUpper 323 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree323.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 323 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel324
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98932433204939565569/20000000000000000000)
  centralHi := (247331083012348913923/50000000000000000000)
  directionLo := (49542967954449726459/10000000000000000000)
  directionHi := (495429679544497264591/100000000000000000000)

def endpointA : IntegerEndpointWitness 324 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree324.table
  base := (49373645322766561190533522386915141617/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-77043727581706781815107379200000000000000)
      constant := (3134766136429688989877642371349532113293600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 324 interval.damping) (curvature.centralUpper 324 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree324.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 324 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree324.table
  base := (9874729064553312210789191630464503587643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4854835246463660232488224353360000000000000)
      constant := (203082637976722725624909199707351803378972535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 324 interval.damping) (curvature.centralUpper 324 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree324.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 324 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel325
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49542967954449726459/10000000000000000000)
  centralHi := (495429679544497264591/100000000000000000000)
  directionLo := (496196005879612844559/100000000000000000000)
  directionHi := (6202450073495160557/1250000000000000000)

def endpointA : IntegerEndpointWitness 325 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree325.table
  base := (2010952772451857709656319499907098258151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-77283422347287240097846175280000000000000)
      constant := (3154777169361637147857461137748141965163020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 325 interval.damping) (curvature.centralUpper 325 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree325.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 325 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree325.table
  base := (502738193112964426217173022160272096039/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4869936016695229104300768506400000000000000)
      constant := (204377074235995404165031437505585333270591100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 325 interval.damping) (curvature.centralUpper 325 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree325.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 325 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel326
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496196005879612844559/100000000000000000000)
  centralHi := (6202450073495160557/1250000000000000000)
  directionLo := (496961150522048672839/100000000000000000000)
  directionHi := (12424028763051216821/2500000000000000000)

def endpointA : IntegerEndpointWitness 326 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree326.table
  base := (5117842134087936002561089283676700414473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-77523117112867698380584971360000000000000)
      constant := (3174851668417822848994627355349413603315784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 326 interval.damping) (curvature.centralUpper 326 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree326.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 326 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree326.table
  base := (5117842134087935992072767805590469859413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4885036786926797976113312659440000000000000)
      constant := (205675610524482084880164756357347330231112370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 326 interval.damping) (curvature.centralUpper 326 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree326.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 326 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel327
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496961150522048672839/100000000000000000000)
  centralHi := (12424028763051216821/2500000000000000000)
  directionLo := (62215639865199370741/12500000000000000000)
  directionHi := (497725118921594965929/100000000000000000000)

def endpointA : IntegerEndpointWitness 327 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree327.table
  base := (10417490277025401646773058568719776646717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-77762811878448156663323767440000000000000)
      constant := (3194989633577135449441719467704879106586868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 327 interval.damping) (curvature.centralUpper 327 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree327.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 327 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree327.table
  base := (5208745138512700814195839741427981283431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4900137557158366847925856812480000000000000)
      constant := (206978246840889740834667240538011710828881190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 327 interval.damping) (curvature.centralUpper 327 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree327.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 327 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel328
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62215639865199370741/12500000000000000000)
  centralHi := (497725118921594965929/100000000000000000000)
  directionLo := (124621979121570230859/25000000000000000000)
  directionHi := (498487916486280923437/100000000000000000000)

def endpointA : IntegerEndpointWitness 328 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree328.table
  base := (1060018188356985575564954692687001237847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-78002506644028614946062563520000000000000)
      constant := (3215191064818622862328398712507480049513880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 328 interval.damping) (curvature.centralUpper 328 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree328.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 328 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree328.table
  base := (2120036376713971147908494312627870591381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4915238327389935719738400965520000000000000)
      constant := (208284983183935056707741732026281141474441725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 328 interval.damping) (curvature.centralUpper 328 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree328.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 328 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel329
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124621979121570230859/25000000000000000000)
  centralHi := (498487916486280923437/100000000000000000000)
  directionLo := (24962477429141068617/5000000000000000000)
  directionHi := (499249548582821372341/100000000000000000000)

def endpointA : IntegerEndpointWitness 329 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree329.table
  base := (10783759082610436534463607568075239981619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-78242201409609073228801359600000000000000)
      constant := (3235455962121489896465512945462300959926476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 329 interval.damping) (curvature.centralUpper 329 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree329.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 329 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree329.table
  base := (431350363304417460813982100146957006251/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-704334156803072084507277874080000000000000)
      constant := (29942259936049189577008911825972587380469625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 329 interval.damping) (curvature.centralUpper 329 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree329.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 329 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel330
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24962477429141068617/5000000000000000000)
  centralHi := (499249548582821372341/100000000000000000000)
  directionLo := (12500250513426432203/2500000000000000000)
  directionHi := (500010020537057288121/100000000000000000000)

def endpointA : IntegerEndpointWitness 330 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree330.table
  base := (5484110934493580178572759281146208090671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-78481896175189531511540155680000000000000)
      constant := (3255784325465096617348783278849169664725368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 330 interval.damping) (curvature.centralUpper 330 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree330.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 330 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree330.table
  base := (10968221868987160344777974503950462027453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4945439867853073463363489271600000000000000)
      constant := (210910755944853355840250630593467863196725985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 330 interval.damping) (curvature.centralUpper 330 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree330.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 330 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel331
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12500250513426432203/2500000000000000000)
  centralHi := (500010020537057288121/100000000000000000000)
  directionLo := (500769337634390295067/100000000000000000000)
  directionHi := (125192334408597573767/25000000000000000000)

def endpointA : IntegerEndpointWitness 331 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree331.table
  base := (5576785118789226751767171009187365921517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-78721590940769989794278951760000000000000)
      constant := (3276176154828956730097565961103498927372136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 331 interval.damping) (curvature.centralUpper 331 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree331.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 331 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree331.table
  base := (11153570237578453492697276703090678750031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4960540638084642335176033424640000000000000)
      constant := (212229792360207357549874512550345216293757595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 331 interval.damping) (curvature.centralUpper 331 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree331.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 331 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel332
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500769337634390295067/100000000000000000000)
  centralHi := (125192334408597573767/25000000000000000000)
  directionLo := (100305501024042249207/20000000000000000000)
  directionHi := (125381876280052811509/25000000000000000000)

def endpointA : IntegerEndpointWitness 332 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree332.table
  base := (11339804183300753288458625721522623610523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-78961285706350448077017747840000000000000)
      constant := (3296631450192735983971175183366090494442092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 332 interval.damping) (curvature.centralUpper 332 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree332.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 332 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree332.table
  base := (2834951045825188319740679392239678446717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4975641408316211206988577577680000000000000)
      constant := (213552928797160859310073566977066884877782660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 332 interval.damping) (curvature.centralUpper 332 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree332.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 332 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel333
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100305501024042249207/20000000000000000000)
  centralHi := (125381876280052811509/25000000000000000000)
  directionLo := (25114226410016148997/5000000000000000000)
  directionHi := (502284528200322979941/100000000000000000000)

def endpointA : IntegerEndpointWitness 333 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree333.table
  base := (11526923701108114497542780885105124072631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-79200980471930906359756543920000000000000)
      constant := (3317150211536250598112108590490420496290524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 333 interval.damping) (curvature.centralUpper 333 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree333.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 333 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree333.table
  base := (576346185055405724461105893935505030701/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4990742178547780078801121730720000000000000)
      constant := (214880165254477604543331509964035974650434900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 333 interval.damping) (curvature.centralUpper 333 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree333.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 333 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel334
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25114226410016148997/5000000000000000000)
  centralHi := (502284528200322979941/100000000000000000000)
  directionLo := (503040412041357353391/100000000000000000000)
  directionHi := (31440025752584834587/6250000000000000000)

def endpointA : IntegerEndpointWitness 334 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree334.table
  base := (11714928785991821043757500981905443328199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-79440675237511364642495340000000000000000)
      constant := (3337732438839465708172248956367621773312796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 334 interval.damping) (curvature.centralUpper 334 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree334.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 334 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree334.table
  base := (11714928785991821036466687340638401457091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5005842948779348950613665883760000000000000)
      constant := (216211501730930457808331187889784408356987295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 334 interval.damping) (curvature.centralUpper 334 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree334.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 334 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel335
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503040412041357353391/100000000000000000000)
  centralHi := (31440025752584834587/6250000000000000000)
  directionLo := (31487197610699165059/6250000000000000000)
  directionHi := (100759032354237328189/20000000000000000000)

def endpointA : IntegerEndpointWitness 335 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree335.table
  base := (11903819432980002760358827269984481611319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-79680370003091822925234136080000000000000)
      constant := (3358378132082493833484620446029937926445276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 335 interval.damping) (curvature.centralUpper 335 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree335.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 335 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree335.table
  base := (11903819432980002753970447560290746016467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5020943719010917822426210036800000000000000)
      constant := (217546938225301310914224736047671232774034415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 335 interval.damping) (curvature.centralUpper 335 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree335.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 335 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel336
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31487197610699165059/6250000000000000000)
  centralHi := (100759032354237328189/20000000000000000000)
  directionLo := (252274391239664698329/50000000000000000000)
  directionHi := (504548782479329396659/100000000000000000000)

def endpointA : IntegerEndpointWitness 336 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree336.table
  base := (2418719127427451449498307655362114875183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-79920064768672281207972932160000000000000)
      constant := (3379087291245593364449802173587242297503660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 336 interval.damping) (curvature.centralUpper 336 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree336.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 336 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree336.table
  base := (96748765097098057935151478625063930253/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-719434927034640956319822027120000000000000)
      constant := (31269496390911570039007355118408654694856875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 336 interval.damping) (curvature.centralUpper 336 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree336.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 336 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel337
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252274391239664698329/50000000000000000000)
  centralHi := (504548782479329396659/100000000000000000000)
  directionLo := (505301279217350867807/100000000000000000000)
  directionHi := (15790664975542214619/3125000000000000000)

def endpointA : IntegerEndpointWitness 337 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree337.table
  base := (12284257393564276691273031175123241012839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-80159759534252739490711728240000000000000)
      constant := (3399859916309167069812263727730492964051356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 337 interval.damping) (curvature.centralUpper 337 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree337.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 337 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree337.table
  base := (3071064348391069171592089027366769553561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5051145259474055566051298342880000000000000)
      constant := (220230111262969165470413582939851434162489780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 337 interval.damping) (curvature.centralUpper 337 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree337.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 337 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel338
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (505301279217350867807/100000000000000000000)
  centralHi := (15790664975542214619/3125000000000000000)
  directionLo := (253026328499629024931/50000000000000000000)
  directionHi := (506052656999258049863/100000000000000000000)

def endpointA : IntegerEndpointWitness 338 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree338.table
  base := (2495160939479495915145236369655120501959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-80399454299833197773450524320000000000000)
      constant := (3420696007253760623508096611993102410039180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 338 interval.damping) (curvature.centralUpper 338 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree338.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 338 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree338.table
  base := (12475804697397479571428689809657032445931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5066246029705624437863842495920000000000000)
      constant := (221577847803874259034899597089957972949253095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 338 interval.damping) (curvature.centralUpper 338 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree338.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 338 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel339
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253026328499629024931/50000000000000000000)
  centralHi := (506052656999258049863/100000000000000000000)
  directionLo := (506802920801889470137/100000000000000000000)
  directionHi := (253401460400944735069/50000000000000000000)

def endpointA : IntegerEndpointWitness 339 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree339.table
  base := (158352969297608090117863157987951794927/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-80639149065413656056189320400000000000000)
      constant := (3441595564060061150771613075746144574376640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 339 interval.damping) (curvature.centralUpper 339 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree339.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 339 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree339.table
  base := (101345900350469177645308835958949434361/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5081346799937193309676386648960000000000000)
      constant := (222929684357913357387113752077890826427305625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 339 interval.damping) (curvature.centralUpper 339 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree339.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 339 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel340
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506802920801889470137/100000000000000000000)
  centralHi := (253401460400944735069/50000000000000000000)
  directionLo := (101510415113059957163/20000000000000000000)
  directionHi := (63444009445662473227/12500000000000000000)

def endpointA : IntegerEndpointWitness 340 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree340.table
  base := (3215388982001141247555036334695756651639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-80878843830994114338928116480000000000000)
      constant := (3462558586708895793194167126155132106426224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 340 interval.damping) (curvature.centralUpper 340 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree340.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 340 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree340.table
  base := (6430777964002282493460448397511468064719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5096447570168762181488930802000000000000000)
      constant := (224285620923912122949528758077980619351712310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 340 interval.damping) (curvature.centralUpper 340 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree340.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 340 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel341
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101510415113059957163/20000000000000000000)
  centralHi := (63444009445662473227/12500000000000000000)
  directionLo := (508300126193139280417/100000000000000000000)
  directionHi := (254150063096569640209/50000000000000000000)

def endpointA : IntegerEndpointWitness 341 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree341.table
  base := (2611151969045333666544904167352299815857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-81118538596574572621666912560000000000000)
      constant := (3483585075181230292434259006777045996317140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 341 interval.damping) (curvature.centralUpper 341 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree341.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 341 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree341.table
  base := (1631969980653333541229221640702807645863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5111548340400331053301474955040000000000000)
      constant := (225645657500704707398729750662025502985891480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 341 interval.damping) (curvature.centralUpper 341 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree341.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 341 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel342
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508300126193139280417/100000000000000000000)
  centralHi := (254150063096569640209/50000000000000000000)
  directionLo := (127261769388257085297/25000000000000000000)
  directionHi := (509047077553028341189/100000000000000000000)

def endpointA : IntegerEndpointWitness 342 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree342.table
  base := (1656356161343836648111278926567606508781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-81358233362155030904405708640000000000000)
      constant := (3504675029458167592283680926730163408280992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 342 interval.damping) (curvature.centralUpper 342 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree342.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 342 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree342.table
  base := (13250849290750693182357424031632958419213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5126649110631899925114019108080000000000000)
      constant := (227009794087133666041965751513542074812707185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 342 interval.damping) (curvature.centralUpper 342 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree342.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 342 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel343
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127261769388257085297/25000000000000000000)
  centralHi := (509047077553028341189/100000000000000000000)
  directionLo := (50979293447692699829/10000000000000000000)
  directionHi := (509792934476926998291/100000000000000000000)

def endpointA : IntegerEndpointWitness 343 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree343.table
  base := (537872970395453242443493369209487077801/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-81597928127735489187144504720000000000000)
      constant := (3525828449520946458799913114670948707780100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 343 interval.damping) (curvature.centralUpper 343 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree343.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 343 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree343.table
  base := (13446824259886331058868162184037979084087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-734535697266209828132366180160000000000000)
      constant := (32625432954578553328608422462417329267943045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 343 interval.damping) (curvature.centralUpper 343 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree343.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 343 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel344
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50979293447692699829/10000000000000000000)
  centralHi := (509792934476926998291/100000000000000000000)
  directionLo := (127634425440374901289/25000000000000000000)
  directionHi := (510537701761499605157/100000000000000000000)

def endpointA : IntegerEndpointWitness 344 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree344.table
  base := (13643684747976888520668989464469561940557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-81837622893315947469883300800000000000000)
      constant := (3547045335350940118220368211297878247762228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 344 interval.damping) (curvature.centralUpper 344 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree344.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 344 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree344.table
  base := (6821842373988444259362314813006973006881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5156850651095037668739107414160000000000000)
      constant := (229750367284312439280652235132741416773371690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 344 interval.damping) (curvature.centralUpper 344 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree344.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 344 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel345
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127634425440374901289/25000000000000000000)
  centralHi := (510537701761499605157/100000000000000000000)
  directionLo := (511281384168474737871/100000000000000000000)
  directionHi := (31955086510529671117/6250000000000000000)

def endpointA : IntegerEndpointWitness 345 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree345.table
  base := (13841430750398951022227378161304330847213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-82077317658896405752622096880000000000000)
      constant := (3568325686929654912379414940795217323388852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 345 interval.damping) (curvature.centralUpper 345 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree345.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 345 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree345.table
  base := (13841430750398951020523811271514089972597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5171951421326606540551651567200000000000000)
      constant := (231126803892788627420501846504920952043286265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 345 interval.damping) (curvature.centralUpper 345 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree345.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 345 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel346
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511281384168474737871/100000000000000000000)
  centralHi := (31955086510529671117/6250000000000000000)
  directionLo := (512023986425000389951/100000000000000000000)
  directionHi := (8000374787890631093/1562500000000000000)

def endpointA : IntegerEndpointWitness 346 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree346.table
  base := (14040062262562051085041574316411908785489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-82317012424476864035360892960000000000000)
      constant := (3589669504238728971354169599145647635141956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 346 interval.damping) (curvature.centralUpper 346 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree346.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 346 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree346.table
  base := (14040062262562051083548990803564930973643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5187052191558175412364195720240000000000000)
      constant := (232507340506353773187032195855801408088542535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 346 interval.damping) (curvature.centralUpper 346 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree346.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 346 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel347
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512023986425000389951/100000000000000000000)
  centralHi := (8000374787890631093/1562500000000000000)
  directionLo := (102553102644798907497/20000000000000000000)
  directionHi := (256382756611997268743/50000000000000000000)

def endpointA : IntegerEndpointWitness 347 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree347.table
  base := (14239579279908340690509974641567088385539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-82556707190057322318099689040000000000000)
      constant := (3611076787259930903070225773196268353542156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 347 interval.damping) (curvature.centralUpper 347 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree347.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 347 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree347.table
  base := (14239579279908340689202253902952960802461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5202152961789744284176739873280000000000000)
      constant := (233891977123891203815686794177175475396602945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 347 interval.damping) (curvature.centralUpper 347 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree347.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 347 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel348
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102553102644798907497/20000000000000000000)
  centralHi := (256382756611997268743/50000000000000000000)
  directionLo := (102701193844898229631/20000000000000000000)
  directionHi := (128376492306122787039/25000000000000000000)

def endpointA : IntegerEndpointWitness 348 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree348.table
  base := (14439981797912267857551568829235511845381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-82796401955637780600838485120000000000000)
      constant := (3632547535975158499603259421716942047381524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 348 interval.damping) (curvature.centralUpper 348 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree348.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 348 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree348.table
  base := (7219990898956133928202911448207972663233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5217253732021313155989284026320000000000000)
      constant := (235280713744292159071101585939093906604984170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 348 interval.damping) (curvature.centralUpper 348 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree348.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 348 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel349
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102701193844898229631/20000000000000000000)
  centralHi := (128376492306122787039/25000000000000000000)
  directionLo := (64280669881497713291/12500000000000000000)
  directionHi := (514245359051981706329/100000000000000000000)

def endpointA : IntegerEndpointWitness 349 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree349.table
  base := (1830158726510032165903370078647311403131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-83036096721218238883577281200000000000000)
      constant := (3654081750366437459917512959706713964900192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 349 interval.damping) (curvature.centralUpper 349 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree349.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 349 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree349.table
  base := (14641269812080257326223134259697591979469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-5232354502252882027801828179360000000000000)
      constant := (236673550366455713014837113078113910034969905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 349 interval.damping) (curvature.centralUpper 349 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree349.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 349 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel349
