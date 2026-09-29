import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell349.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch300_349
import ForestUnimodality.BinomialMassData.Q9_35.Batch300_349

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel300
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
  base := (13531243744040432043008468494083148256629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-80480133287807698594384930760000000000000)
      constant := (3045898403399178599999189730976332593026516) }

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
  base := (13531243744040431876525723823775183041853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5071472537059141029967823660050000000000000)
      constant := (197276506530632577675812706437824919845253985) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel301
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
  base := (6877857952672264478361316386717983656813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-80750732093866592863073972000000000000000)
      constant := (3066950150217104274086228750938743869254504) }

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
  base := (3438928976336132202700903961972933920187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-103847352282466354467249658330000000000000)
      constant := (4053832387726164907090239886625458678403740) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel302
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
  base := (13981343235457953759083105879943129571239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-81021330899925487131763013240000000000000)
      constant := (3088074167411781983295025266519772518284956) }

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
  base := (13981343235457953631189058417513205660087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5105567986622561707822642856290000000000000)
      constant := (200003734183548022638279914803206735386721315) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel303
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
  base := (14208125728564722477899704909601372188477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-81291929705984381400452054480000000000000)
      constant := (3109270454959947791736818546103405488753908) }

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
  base := (14208125728564722365805136711299445977999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5122615711404272046750052454410000000000000)
      constant := (201374348084105488175277343382274364264609755) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel304
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
  base := (14436063378895919958132796035093907527641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-81562528512043275669141095720000000000000)
      constant := (3130539012838526038791450054380375630110564) }

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
  base := (7218031689447959929943425310866858831869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5139663436185982385677462052530000000000000)
      constant := (202749628698841092845496615155508760827615810) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel305
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
  base := (2933031236145833728081606244996240377163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-81833127318102169937830136960000000000000)
      constant := (3151879841024627214221422399224924807543260) }

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
  base := (2933031236145833710860122675856474950369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5156711160967692724604871650650000000000000)
      constant := (204129576026352854146950001364374181814202025) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel306
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
  base := (1861925516048513127216479739502613917449/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-82103726124161064206519178200000000000000)
      constant := (3173292939495545863998761290384083645358368) }

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
  base := (2979080825677620988452783311208235173227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5173758885749403063532281248770000000000000)
      constant := (205514190065250063020475787444034088087203075) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel307
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
  base := (15126807216241863635278500887417453972821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-82374324930219958475208219440000000000000)
      constant := (3194778308228758526304163866974669815891284) }

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
  base := (7563403608120931784568036452684814391021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5190806610531113402459690846890000000000000)
      constant := (206903470814153157429687005019061559051600290) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel308
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
  base := (7679682719352284250480686191640704325681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-82644923736278852743897260680000000000000)
      constant := (3216335947201921697169283537973125634605448) }

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
  base := (3839841359676142110748159102190251274709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-106282741536996402885451029490000000000000)
      constant := (4250967719830481586868615608467805025494180) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel309
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
  base := (15593078790234831777191456770666554080061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-82915522542337747012586301920000000000000)
      constant := (3237965856392869825243764320847666216320244) }

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
  base := (7796539395117415863193400675738158006183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5224902060094534080314510043130000000000000)
      constant := (209696032436513743980926799431505697423029670) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel310
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
  base := (15827947265335259626928713044170097276843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-83186121348396641281275343160000000000000)
      constant := (3259668035779613335179446051576680389107372) }

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
  base := (316558945306705191648063448781693355777/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5241949784876244419241919641250000000000000)
      constant := (211099313307266734612736637021675743608268250) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel311
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
  base := (16063970858551965089709225555712382259163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-83456720154455535549964384400000000000000)
      constant := (3281442485340336679134473067567849529036652) }

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
  base := (8031985429275982525343549520910371143553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5258997509657954758169329239370000000000000)
      constant := (212507260882616367346704788181140081860340970) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel312
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
  base := (16301149564474087865891761317170485967853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-83727318960514429818653425640000000000000)
      constant := (3303289205053396415910280436868681943871412) }

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
  base := (16301149564474087831693129366787369001249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5276045234439665097096738837490000000000000)
      constant := (213919875161236981409442617220638905405306005) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel313
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
  base := (16539483377733320889834215362089919257589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-83997917766573324087342466880000000000000)
      constant := (3325208194897319317244299739613359677030356) }

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
  base := (3307896675546664171972623777402641663921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5293092959221375436024148435610000000000000)
      constant := (215337156141813341569888378731064236038303225) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel314
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
  base := (16778972293003443575159745862080660830333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-84268516572632218356031508120000000000000)
      constant := (3347199454850800500791023608488322643321332) }

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
  base := (1677897229300344354889382352313167448639/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5310140684003085774951558033730000000000000)
      constant := (216759103823040523784397777912971260249165550) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel315
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
  base := (17019616304999861617601635968463919661969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-84539115378691112624720549360000000000000)
      constant := (3369262984892701589333385176098855678647876) }

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
  base := (8509808152499930797291519901522716015041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-108718130791526451303652400650000000000000)
      constant := (4452769759257628621396760712565227160150410) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel316
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
  base := (17261415408479153243274573588598836839027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-84809714184750006893409590600000000000000)
      constant := (3391398785002048895775843194074395347356108) }

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
  base := (17261415408479153223102005354584437312023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5344236133566506452806377229970000000000000)
      constant := (219616999282278539227430822958057187141445635) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel317
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
  base := (1750436959823862179244183666325516797927/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-85080312990808901162098631840000000000000)
      constant := (3413606855158031633479450774178020671917080) }

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
  base := (17504369598238621774763566716411617053209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5361283858348216791733786828090000000000000)
      constant := (221052947057730073439743069442026846178036205) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel318
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
  base := (17748478869115854531069919316749146812651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-85350911796867795430787673080000000000000)
      constant := (3435887195340000151508073892906996587250604) }

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
  base := (3549695773823170903115533373318099288367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5378331583129927130661196426210000000000000)
      constant := (222493561528713613965550450397230671628249575) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel319
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
  base := (899687160799414379231190384000054589047/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-85621510602926689699476714320000000000000)
      constant := (3458239805527464194363572494785004367123760) }

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
  base := (3598748643197657514209475239945588421463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5395379307911637469588606024330000000000000)
      constant := (223938842693974132655601218070347345816292175) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel320
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
  base := (18240162633772776890651967846720421687971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-85892109408985583968165755560000000000000)
      constant := (3480664685700091185796140444186881686751884) }

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
  base := (9120081316886388439377271252387535243569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5412427032693347808516015622450000000000000)
      constant := (225388790552266259214602925169669892269348810) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel321
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
  base := (18487737117425175068769258902319622821653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-86162708215044478236854796800000000000000)
      constant := (3503161835837704536284237177454278491286612) }

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
  base := (4621934279356293764585821090604049203727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5429474757475058147443425220570000000000000)
      constant := (226843405102354177534368380747465968219652460) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel322
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
  base := (18736466661939914108664680180380621456101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-86433307021103372505543838040000000000000)
      constant := (3525731255920281973786618691921522485824404) }

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
  base := (18736466661939914099528247182139754184957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-111153520046056499721853771810000000000000)
      constant := (4659238496796153539844442304674698770924785) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel323
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
  base := (18986351262349593778715608684332852314161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-86703905827162266774232879280000000000000)
      constant := (3548372945927953897376794495602331409256644) }

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
  base := (2373293907793699221338660830242319645007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5463570207038478825298244416810000000000000)
      constant := (229766634273021283911888766355560946504213720) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel324
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
  base := (601168466053892989366283885210384245021/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-86974504633221161042921920520000000000000)
      constant := (3571086905841001753377960748146929183362688) }

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
  base := (19237390913724575652705144920995205955071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5480617931820189164225654014930000000000000)
      constant := (231235248891175697500202252860867825458992395) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel325
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
  base := (19489585611172582710134185751819750293197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-87245103439280055311610961760000000000000)
      constant := (3593873135639856433623929764132279001172788) }

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
  base := (19489585611172582703986169275554554083707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5497665656601899503153063613050000000000000)
      constant := (232708530196276156342143367522760865750508215) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel326
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
  base := (157943482798706434168073061924283721401/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-87515702245338949580300003000000000000000)
      constant := (3616731635305096695478918422682141860700500) }

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
  base := (19742935349838304265621714905646849975607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5514713381383609842080473211170000000000000)
      constant := (234186478187133109326274102365247478244023715) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel327
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
  base := (4999360031225751605172622275342352837257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-87786301051397843848989044240000000000000)
      constant := (3639662404817447603256304979030477645396112) }

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
  base := (4999360031225751603992402807862072978473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5531761106165320181007882809290000000000000)
      constant := (235669092862565966641792125596270831518903540) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel328
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
  base := (4050619986316829518196497996497006983473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-88056899857456738117678085480000000000000)
      constant := (3662665444157778990683306373769940139669460) }

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
  base := (405061998631682951736914401746650122727/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5548808830947030519935292407410000000000000)
      constant := (237156374221403005604492323365252464003405750) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel329
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
  base := (4101982953026999871660758389652110038353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-88327498663515632386367126720000000000000)
      constant := (3685740753307103944065597233158042200767060) }

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
  base := (20509914765134999354678888185755451711353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-113588909300586548140055142970000000000000)
      constant := (4870373923724107709195913532994777258556765) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel330
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
  base := (324498197200691755077567335131114267091/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-88598097469574526655056167960000000000000)
      constant := (3708888332246577305812417214993565252375296) }

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
  base := (20767884620844272321787960993927283586059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5582904280510451197790111603650000000000000)
      constant := (240144936984646517177682561990212184478584455) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel331
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
  base := (164273511672154273495010404486254741427/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-88868696275633420923745209200000000000000)
      constant := (3732108180957494197989355476441962427610624) }

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
  base := (21027009494035747004578055199461778675051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5599952005292161536717521201770000000000000)
      constant := (241646218386753050112259973574122135775387495) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel332
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
  base := (4257457876013581929897680176068110135919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-89139295081692315192434250440000000000000)
      constant := (3755400299421288565572386185321362202718380) }

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
  base := (21287289380067909647049572844487776738913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5616999730073871875644930799890000000000000)
      constant := (243152166467663705684112096368795505301033685) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel333
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
  base := (4309744854866718576343081356367009422223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-89409893887751209461123291680000000000000)
      constant := (3778764687619531739082988901692340188444460) }

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
  base := (21548724274333592879578416207489594859687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5634047454855582214572340398010000000000000)
      constant := (244662781226249727887681026432460950740623315) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel334
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
  base := (2726414271532452643291866995472161714813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-89680492693810103729812332920000000000000)
      constant := (3802201345533931016290333971495109174874016) }

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
  base := (21811314172259621144462440945204583309173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5651095179637292553499749996130000000000000)
      constant := (246178062661390688711329738401019122910747385) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel335
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
  base := (22075059069306460812854735830638792738883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-89951091499868997998501374160000000000000)
      constant := (3825710273146328262672452384347555170955532) }

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
  base := (22075059069306460811214012343284145115729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5668142904419002892427159594250000000000000)
      constant := (247698010771974402415588761769454615553353605) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel336
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
  base := (22339958960967874907505396832704882856791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-90221690305927892267190415400000000000000)
      constant := (3849291470438698530334266502050819531427164) }

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
  base := (22339958960967874906067767908236493516327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-116024298555116596558256514130000000000000)
      constant := (5086176031773404917181338422997182467581635) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel337
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
  base := (2260601384277058238283888823375812305917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-90492289111986786535879456640000000000000)
      constant := (3872944937393148695085984201660032492236680) }

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
  base := (5651503460692645595394805916015579764843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5702238353982423570281978790490000000000000)
      constant := (250751907015062050433596302699121268169546140) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel338
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
  base := (11436611855136960927355458773843983803187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-90762887918045680804568497880000000000000)
      constant := (3896670673991916111391028313230751870425496) }

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
  base := (22873223710273921853607195407662085350259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5719286078764133909209388388610000000000000)
      constant := (252285855145382068851606331556473210910813455) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel339
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
  base := (5785397139767379933827271081258841113673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-91033486724104575073257539120000000000000)
      constant := (3920468680217367284898149234965141457818768) }

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
  base := (23141588559069519734342006679168927778679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5736333803545844248136797986730000000000000)
      constant := (253824469946776844666902298566250387305776355) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel340
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
  base := (585277709619524067305793224401603115493/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-91304085530163469341946580360000000000000)
      constant := (3944338956051996562277740328504256498478880) }

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
  base := (23411108384780962691384385076302832930829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5753381528327554587064207584850000000000000)
      constant := (255367751418174156613046381989894194068053105) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel341
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
  base := (23681783183063474364924946562479656251153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-91574684336222363610635621600000000000000)
      constant := (3968281501478424838087585974094918625004612) }

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
  base := (2960222897882934295522814708885498368207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5770429253109264925991617182970000000000000)
      constant := (256915699558509534481703387660049576801685720) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel342
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
  base := (11976806474801798135542761406510222523349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-91845283142281257879324662840000000000000)
      constant := (3992296316479398278398473314652081780186792) }

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
  base := (23953612949603596270435023508400993208091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5787476977890975264919026781090000000000000)
      constant := (258468314366726180944709477242714243335982295) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel343
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
  base := (24226597680118872836881865601484356887759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-92115881948340152148013704080000000000000)
      constant := (4016383401037787060915075981670937427551036) }

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
  base := (4845319536023774567262383411978345268727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-118459687809646644976457885290000000000000)
      constant := (5306644813097446824213802128233458631718175) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel344
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
  base := (12250368685178770243037544446536604594689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-92386480754399046416702745320000000000000)
      constant := (4040542755136584131332438431012292836757512) }

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
  base := (24500737370357540485575720195564125730327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5821572427454395942773845977330000000000000)
      constant := (261587543982613992730825686640377210803930115) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel345
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
  base := (24776032016098220724339704434558501026933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-92657079560457940685391786560000000000000)
      constant := (4064774378758903975673258709663234004107732) }

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
  base := (12388016008049110361951089218257973387921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5838620152236106281701255575450000000000000)
      constant := (263154158788209238246648181966196406960081290) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel346
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
  base := (1565780100821851072264864242691823666203/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-92927678366516834954080827800000000000000)
      constant := (4089078271887981408355785280252276714636992) }

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
  base := (12526240806574808577927244305597768418417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5855667877017816620628665173570000000000000)
      constant := (264725440257533763317061773483866906525024330) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel347
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
  base := (3166260769668777046685453177000467897339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-93198277172575729222769869040000000000000)
      constant := (4113454434507170375746874807489014972714848) }

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
  base := (25330086157350216373147764332560437755309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5872715601799526959556074771690000000000000)
      constant := (266301388389567997157036664028563307250050705) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel348
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
  base := (25608845644567992654222781769649474629333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-93468875978634623491458910280000000000000)
      constant := (4137902866599942774959110030318597898517332) }

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
  base := (25608845644567992653928520572296782404481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5889763326581237298483484369810000000000000)
      constant := (267882003183299593464718749768348711689097845) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel349
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
  base := (25888760070700116414208256511039962407631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-93739474784693517760147951520000000000000)
      constant := (4162423568149887287655502787009159849630524) }

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
  base := (25888760070700116413950444424645959586003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5906811051362947637410893967930000000000000)
      constant := (269467284637723358991967684041312260098570735) }

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
end ForestUnimodality.Stage170KernelData.Cell349.Kernel349
