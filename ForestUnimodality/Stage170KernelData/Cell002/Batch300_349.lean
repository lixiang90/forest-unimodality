import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell002.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch300_349
import ForestUnimodality.BinomialMassData.Q9_35.Batch300_349

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel300
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
  base := (-706305233833311582524487313710580156373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26279756573184967251288757220000000000000)
      constant := (969792991667519959760831743362894198436270) }

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
  base := (-882881542291639780588462888380234379351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1656027622726786819326930121225000000000000)
      constant := (62898745074815275312303524339193685154118010) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel301
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
  base := (-3464455368661429339509540081695554082937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26368123301983457870689697680000000000000)
      constant := (976508118252926270047304843199108891834126) }

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
  base := (-3464455368661430397667290403290221200507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-474741350468883350956911248630000000000000)
      constant := (18095289340798823092263343024610842257982255) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel302
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
  base := (-212306501114275721469814908534883789597/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26456490030781948490090638140000000000000)
      constant := (983246297621187981434387388266883718732896) }

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
  base := (-3396904017828412469106963941419189238451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3334323661110793274742897238370000000000000)
      constant := (127539541438396376618097416638420298636579505) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel303
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
  base := (-104027253870882705870492104827955839627/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26544856759580439109491578600000000000000)
      constant := (990007529757903609795657747723510826263872) }

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
  base := (-3328872123868247397498587915278628727883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3345457868939403092787415736330000000000000)
      constant := (128415038306280213736466794718714735961668665) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel304
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
  base := (-1630179846961700428525068643252243470983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26633223488378929728892519060000000000000)
      constant := (996791814648788222362066980066991026116068) }

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
  base := (-163017984696170078264055585395699460011/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1678296038384006455415967117145000000000000)
      constant := (64646757993746684368626996407156536322973050) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel305
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
  base := (-398920841884840344971187847839806423487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26721590217177420348293459520000000000000)
      constant := (1003599152279672122316276496397063097224208) }

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
  base := (-3191366735078723379300222655960379942459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3367726284596622728876452732250000000000000)
      constant := (130174974480300053760781817527739706914097545) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel306
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
  base := (-780473313590522731327548124797953811323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26809956945975910967694399980000000000000)
      constant := (1010429542636499552399693599401616369509416) }

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
  base := (-1560946627181045733628826288847007757091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1689430246212616273460485615105000000000000)
      constant := (65529706891489219271631672281758483099512705) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel307
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
  base := (-1525969629372526530516168920569323487589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26898323674774401587095340440000000000000)
      constant := (1017282985705327417197598026270222706049644) }

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
  base := (-610387851749010707023825044120989516679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3389994700253842364965489728170000000000000)
      constant := (131946833893820493896736971603509787842068225) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel308
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
  base := (-2981504755143455634536138029558502430497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-26986690403572892206496280900000000000000)
      constant := (1024159481472324023774789378560882995139006) }

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
  base := (-2981504755143456049265481250191624389887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-485875558297493169001429746590000000000000)
      constant := (18976747830161691062419913240667293146353955) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel309
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
  base := (-1455294875209032270515664835341374063697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27075057132371382825897221360000000000000)
      constant := (1031059029923767840340848183061134503745212) }

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
  base := (-181911859401129056490009544150781354383/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1706131557955531000527263362045000000000000)
      constant := (66865308266615790759902733478605468545409320) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel310
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
  base := (-2839194251375176913007950096665072741257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27163423861169873445298161820000000000000)
      constant := (1037981631046046272630794365106669854517486) }

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
  base := (-2839194251375177230400697646003221151721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3423397323739671819099045222050000000000000)
      constant := (134626979058452183348103592697229210817828355) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel311
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
  base := (-2767318264767224226124876293620911901613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27251790589968364064699102280000000000000)
      constant := (1044927284825654457693310170725258176196774) }

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
  base := (-691829566191806125947632120077761450501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1717265765784140818571781860005000000000000)
      constant := (67763161192569648605248566931972896889254510) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel312
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
  base := (-269496179729336685206259240411591386331/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27340157318766854684100042740000000000000)
      constant := (1051895991249194074785034631631768172273380) }

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
  base := (-673740449323341773744245647886142398891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1722832869698445727594041108985000000000000)
      constant := (68214323255825814408049546399359790224543410) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel313
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
  base := (-524424971120016041206447135936488539679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27428524047565345303500983200000000000000)
      constant := (1058887750303372173075545473323135114603210) }

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
  base := (-524424971120016083709503812187453728129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3456799947225501273232600715930000000000000)
      constant := (137333951436360791688335542026648369183041975) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel314
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
  base := (-2548807446281732633600466370575525482651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27516890776363835922901923660000000000000)
      constant := (1065902561975000015873709375298848949034698) }

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
  base := (-637201861570433204880838618982286835117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1733967077527055545638559606945000000000000)
      constant := (69121118578825582791338141741904679450792670) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel315
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
  base := (-2475009575881155178605859325136362374063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27605257505162326542302864120000000000000)
      constant := (1072940426250991941091849187862227275251874) }

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
  base := (-2475009575881155341266032361879035533609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-497009766126102987045948244550000000000000)
      constant := (19879071953417108127642534143784233756323685) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel316
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
  base := (-2400731250890203371022248098232803117547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27693624233960817161703804580000000000000)
      constant := (1080001343118364237670017243903534393764906) }

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
  base := (-96029250035608140533287176381667525887/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3490202570711330727366156209810000000000000)
      constant := (140067750983576061016058535055454286403942125) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel317
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
  base := (-2325972477750311170873632161111755185381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27781990962759307781104745040000000000000)
      constant := (1087085312564234037688165544480276489629238) }

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
  base := (-581493119437577823845225958236840268729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1750668389269970272705337353885000000000000)
      constant := (70492489542520963315121095059132948268322790) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel318
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
  base := (-450146652570607440310825895697308435401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27870357691557798400505685500000000000000)
      constant := (1094192334575818223899505853663026915645990) }

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
  base := (-2250733262853037310487182415825245677369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3512470986368550363455193205730000000000000)
      constant := (141905187976751421873395334882910814809044595) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel319
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
  base := (-1087506806270301701615040202048534480413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-27958724420356289019906625960000000000000)
      constant := (1101322409140432352423705490744305862078348) }

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
  base := (-5437534031351508746345558939149064961/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1761802597098580090749855851845000000000000)
      constant := (71414188828575351185122801643552695816911000) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel320
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
  base := (-419762706621285246881305219205769393763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28047091149154779639307566420000000000000)
      constant := (1108475536245489590343754373407942306062370) }

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
  base := (-2098813533106426317794925956605362534501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3534739402025769999544230201650000000000000)
      constant := (143754548124697881088519075163031686179047255) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel321
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
  base := (-1011066515397820273595423022674084192397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28135457877953270258708506880000000000000)
      constant := (1115651715878499667955437742671803663230412) }

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
  base := (-1011066515397820310075563252571153840691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1772936804927189908794374349805000000000000)
      constant := (72341849688931449994750880229401067309030705) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel322
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
  base := (-1944972111805616259286988771679105168911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28223824606751760878109447340000000000000)
      constant := (1122850948027067845423347701496641789662178) }

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
  base := (-972486055902808161561996424247252560037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-254071986977356402545233371255000000000000)
      constant := (10401130815366243103100139507553346160398705) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel323
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
  base := (-373466156457293588666711257087223202941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28312191335550251497510387800000000000000)
      constant := (1130073232678893893602207045861627767970590) }

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
  base := (-1867330782286467999188751311117563742053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3568142025511599453677785695530000000000000)
      constant := (146550944234984613379963222654374196883197015) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel324
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
  base := (-5591278276067367036901104122643965761/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28400558064348742116911328260000000000000)
      constant := (1137318569821771088787060166301507861912960) }

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
  base := (-894604524170778750340150510449302973313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1789638116670104635861152096745000000000000)
      constant := (73744518917969603072681759409175920771538315) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel325
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
  base := (-855303458013994846704939868798902303317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28488924793147232736312268720000000000000)
      constant := (1144586959443585221160510063087304390786732) }

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
  base := (-1710606916027989736172139579407093951033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3590410441168819089766822691450000000000000)
      constant := (148430112216507191037002334685295261981996915) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel326
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
  base := (-81576219567855083727679908974212247619/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28577291521945723355713209180000000000000)
      constant := (1151878401532313616709725810941031510095240) }

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
  base := (-1631524391357101711970386073467124464279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3601544648997428907811341189410000000000000)
      constant := (149374167375215790488334671078932554506251645) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel327
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
  base := (-2424939812960851433402654253833481333/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28665658250744213975114149640000000000000)
      constant := (1159192896076024172390431029707593143893760) }

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
  base := (-775980740147472475058791379039305515371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1806339428413019362927929843685000000000000)
      constant := (75160601655301660938230052573394370148734105) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel328
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
  base := (-1471918188762761363535129302851377497039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28754024979542704594515090100000000000000)
      constant := (1166530443062874404319319823514297245005922) }

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
  base := (-735959094381380696091504386857549834971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1811906532327324271950189092665000000000000)
      constant := (75635610010609540462847081749723900290432105) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel329
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
  base := (-86962157664840804428787618736445374049/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28842391708341195213916030560000000000000)
      constant := (1173891042481110508780722768402933748030432) }

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
  base := (-1391394522637452895928184980231546826473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-519278181783322623134985240470000000000000)
      constant := (21746316786517603811555039075177895861073445) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel330
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
  base := (-262078097550408881596298961389443413887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-28930758437139685833316971020000000000000)
      constant := (1181274694319066435837385107786105565861130) }

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
  base := (-1310390487752044429916463193190615070511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3646081480311868179989415181250000000000000)
      constant := (153180195762386668024735414032368299307724805) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel331
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
  base := (-1228906089896141049885672888656856399481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29019125165938176452717911480000000000000)
      constant := (1188681398565162975339331111935186287201038) }

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
  base := (-1228906089896141069079698078486236478373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3657215688140477998033933679210000000000000)
      constant := (154139154790090951713886280624672872062798615) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel332
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
  base := (-573470667408189437741445082847857095991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29107491894736667072118851940000000000000)
      constant := (1196111155207906855128741272808608571616036) }

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
  base := (-286735333704094723069661345237456703923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1834174947984543908039226088585000000000000)
      constant := (77550547293664075954508494072837646215077730) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel333
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
  base := (-1064496228216869866258846626741050678221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29195858623535157691519792400000000000000)
      constant := (1203563964235889851242644190429017898643558) }

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
  base := (-33265507131777183779879384673980375409/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1839742051898848817061485337565000000000000)
      constant := (78033007576350380587337020984586996928396720) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel334
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
  base := (-981570775759640903218538002779097181889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29284225352333648310920732860000000000000)
      constant := (1211039825637787909919029873334441805636222) }

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
  base := (-981570775759640916079679013913351220333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3690618311626307452167489173090000000000000)
      constant := (157033916484821582925020405538523228951018415) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel335
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
  base := (-898164983065066957477177218207859763321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29372592081132138930321673320000000000000)
      constant := (1218538739402360281215667895676084280473358) }

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
  base := (-44908249153253348436583402375099899877/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1850876259727458635106003835525000000000000)
      constant := (79002399291156812646070444624056005245301350) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel336
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
  base := (-407139427856149284006572607649758395671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29460958809930629549722613780000000000000)
      constant := (1226060705518448664054601495569400966417316) }

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
  base := (-101784856964037322232723429003359354991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-265206194805966220589751869215000000000000)
      constant := (11355618674557856885285201535187529690301260) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel337
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
  base := (-9123904990496046229450047974655989823/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29549325538729120169123554240000000000000)
      constant := (1233605723974976362508771549326555041628320) }

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
  base := (-91239049904960463371811180362897760919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1862010467556068453150522333485000000000000)
      constant := (79977752533976900489758805732293360194299380) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel338
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
  base := (-645065619145184062227807549607261929503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29637692267527610788524494700000000000000)
      constant := (1241173794760947453150733948020785476140994) }

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
  base := (-32253280957259203488493032589777790543/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1867577571470373362172781582465000000000000)
      constant := (80467664726699019214429368976969044413169650) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel339
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
  base := (-279869260443393003230498193880002678001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29726058996326101407925435160000000000000)
      constant := (1248764917865445963286823811576979989287996) }

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
  base := (-559738520886786013061121549726102737707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3746289350769356542390081662890000000000000)
      constant := (161918134598805502087046961940379104829261785) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel340
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
  base := (-473931109882906037853476283830742780021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29814425725124592027326375620000000000000)
      constant := (1256379093277635059903445328132338514439958) }

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
  base := (-473931109882906043629362813629085092677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3757423558597966360434600160850000000000000)
      constant := (162903920502848679909920916208060874152294135) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel341
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
  base := (-77528678302558215801757439671297760981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29902792453923082646727316080000000000000)
      constant := (1264016320986756249155391417765787022390190) }

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
  base := (-193821695756395542031706244251929979979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1884278883213288089239559329405000000000000)
      constant := (81946343582104828200723168942979277154905145) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel342
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
  base := (-300875371116913536599379197988928074139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-29991159182721573266128256540000000000000)
      constant := (1271676600982128586229317180344022143851722) }

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
  base := (-12035014844676541640913952320144488591/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3779691974255185996523637156770000000000000)
      constant := (164884434581580015821991630306827115007380125) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel343
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
  base := (-106813526998680631975217112724189123163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-30079525911520063885529197000000000000000)
      constant := (1279359933253147895418572251981603243507348) }

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
  base := (-106813526998680633910795839726556212171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-270773298720271129612011118195000000000000)
      constant := (11848511625261481903392491649526570532574015) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel344
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
  base := (-125898445418222498318709865495660537853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-30167892640318554504930137460000000000000)
      constant := (1287066317789286000248643117509008678924294) }

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
  base := (-62949222709111250853272501915549918497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1900980194956202816306337076345000000000000)
      constant := (83438435839581073629915302394926690269968235) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel345
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
  base := (-37689550605965851733749701885927908987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-30256259369117045124331077920000000000000)
      constant := (1294795754580089963495470689758728144182026) }

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
  base := (-37689550605965854698630811536932284327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3813094597741015450657192650650000000000000)
      constant := (167877561356803732849053669498823451590339885) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel346
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
  base := (25499812625092283580258197590098332833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-30344626097915535743732018380000000000000)
      constant := (1302548243615181336941767108990360393331332) }

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
  base := (25499812625092282282882303701240638359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1912114402784812634350855574305000000000000)
      constant := (84440615892657071754274081289612803956397955) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel347
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
  base := (70084538498939412145101053080950306337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-30432992826714026363132958840000000000000)
      constant := (1310323784884255420719384602564823801225348) }

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
  base := (70084538498939411009677699106285057297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1917681506699117543373114823285000000000000)
      constant := (84943941481715526752233799498320039839037765) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel348
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
  base := (114909399760637774867730308911944739989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-30521359555512516982533899300000000000000)
      constant := (1318122378377080532088483476855647778959956) }

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
  base := (114909399760637773874035036579745390097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1923248610613422452395374072265000000000000)
      constant := (85448757444950540850591515618286037620573765) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel349
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
  base := (319948787740680972519422621993381808361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-30609726284311007601934839760000000000000)
      constant := (1325944024083497283507109993246486763616722) }

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
  base := (63989757548136194156018543904061424007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-3857631429055454722835266642490000000000000)
      constant := (171910127563479703124806364400404475244408575) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel349
