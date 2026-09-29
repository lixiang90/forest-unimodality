import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell028.Parameters
import ForestUnimodality.BinomialMassData.Q17_37.Batch000_049
import ForestUnimodality.BinomialMassData.Q17_37.Batch050_099
import ForestUnimodality.BinomialMassData.Q17_37.Batch100_149
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch000_049
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch050_099
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree000.table
  base := (4158343151259876329216780247/100000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1820)
      previous := (1547)
      next := (0)
      square := (42625697953979695131732085500000000000000)
      linear := (186721108345632349490017530100000000000000)
      constant := (15385869659661542418102086913900000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree000.table
  base := (4158343151259876329216780247/100000000000000000000000000)
  polynomial :=
    { denominator := 34780000000000000000000000000000000000000000
      center := (169715)
      previous := (146783)
      next := (0)
      square := (4006815607674091342382816037000000000000000)
      linear := (17551784184489440852061647829400000000000000)
      constant := (1446271748008184987301596169906600000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree001.table
  base := (256465826903950193558424433778797406634853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (5459407278353087296651757706700000000000000)
      constant := (348260399452029365902127632174973649683113757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree001.table
  base := (50994816402178616783233954448887715944567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (24059559121648828306471723307645600000000000000)
      constant := (1529488116427370081677401147676718334299999006070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49835375444826417891/100000000000000000000)
  directionHi := (12458843861206604473/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree002.table
  base := (163596187001345268368729053679887008543143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (4010133547917777662172866799700000000000000)
      constant := (218946427370679375962028999838365314695562767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree002.table
  base := (80933402453338474056112738224687264317879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (17596565546470518971208241039964600000000000000)
      constant := (956693294522519362202952886309822697824994237436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49835375444826417891/100000000000000000000)
  centralHi := (12458843861206604473/25000000000000000000)
  directionLo := (550608311250223709/781250000000000000)
  directionHi := (70477863840028634753/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree003.table
  base := (108553934888910189158092909033114496620679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (2560859817482468027693975892700000000000000)
      constant := (142084031698866506891212221522733745873709551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree003.table
  base := (53512677013595188605725306826993840124339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (11133571971292209635944758772283600000000000000)
      constant := (618336807239645051964152664791524205162624724076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550608311250223709/781250000000000000)
  centralHi := (70477863840028634753/100000000000000000000)
  directionLo := (86317402284709794589/100000000000000000000)
  directionHi := (8631740228470979459/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree004.table
  base := (9390446428446434541459103921402226260337/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (1111586087047158393215084985700000000000000)
      constant := (95474194115199165124336999596397182003210824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree004.table
  base := (923675356219227588922634871416271312419/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (4670578396113900300681276504602600000000000000)
      constant := (414285769207769473854280259009622930813417391840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86317402284709794589/100000000000000000000)
  centralHi := (8631740228470979459/10000000000000000000)
  directionLo := (99670750889652835783/100000000000000000000)
  directionHi := (12458843861206604473/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree005.table
  base := (27064396479341054151752384675002256071199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-337687643388151241263805921300000000000000)
      constant := (66554554910989578110218547769156177122942862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree005.table
  base := (13292843753513621588501417945340150102517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-1792415179064409034582205763078400000000000000)
      constant := (288282739894621466250944653231228250545390500456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99670750889652835783/100000000000000000000)
  centralHi := (12458843861206604473/12500000000000000000)
  directionLo := (22287057435771138107/20000000000000000000)
  directionHi := (13929410897356961317/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree006.table
  base := (8074941827735514235474765246940291570153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-1786961373823460875742696828300000000000000)
      constant := (48213309205897926324938672411106295797697285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree006.table
  base := (19814500615174251493335470664161108781393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-8255408754242718369845688030759400000000000000)
      constant := (208705137118282176756291670822770625796379922212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22287057435771138107/20000000000000000000)
  centralHi := (13929410897356961317/12500000000000000000)
  directionLo := (23842039253877143/19531250000000000)
  directionHi := (122071240979850972161/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree007.table
  base := (15453704443456237949230435547161432261281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-3236235104258770510221587735300000000000000)
      constant := (36406552730520672152449983277728001531387378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree007.table
  base := (30314652796605029441089644012267966001551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-14718402329421027705109170298440400000000000000)
      constant := (157697012125516453737553058421375677225152823342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23842039253877143/19531250000000000)
  centralHi := (122071240979850972161/100000000000000000000)
  directionLo := (8240750620034099977/6250000000000000000)
  directionHi := (131852009920545599633/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree008.table
  base := (300490859128100237541913787729616768563/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-4685508834694080144700478642300000000000000)
      constant := (28823928950130793651340355922547628493019760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree008.table
  base := (11776492135862855752398973210293614719661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-21181395904599337040372652566121400000000000000)
      constant := (125125470254964705116028135299888545758543771924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8240750620034099977/6250000000000000000)
  centralHi := (131852009920545599633/100000000000000000000)
  directionLo := (550608311250223709/390625000000000000)
  directionHi := (28191145536011453901/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree009.table
  base := (9399532548427048496047775036070093622117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-6134782565129389779179369549300000000000000)
      constant := (24135832794892879130171433766959916337356346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree009.table
  base := (9192959939058107542939556548982895851711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-27644389479777646375636134833802400000000000000)
      constant := (105195837349398220474954241574588665943888484124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550608311250223709/390625000000000000)
  centralHi := (28191145536011453901/20000000000000000000)
  directionLo := (5980245053379170147/4000000000000000000)
  directionHi := (37376531583619813419/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree010.table
  base := (14621712539710617982688023156383090421621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-7584056295564699413658260456300000000000000)
      constant := (21568662287836422802484957934088450787199149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree010.table
  base := (7129586101541228216769600297724727060277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-34107383054955955710899617101483400000000000000)
      constant := (94555648999289309321261915131886397289007766068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5980245053379170147/4000000000000000000)
  centralHi := (37376531583619813419/25000000000000000000)
  directionLo := (2462395225863724861/1562500000000000000)
  directionHi := (31518658891055678221/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree011.table
  base := (11173114154256588556052005275846364948203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-9033330026000009048137151363300000000000000)
      constant := (20665038766617424677562438657433673614089907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree011.table
  base := (10846547710424768248765644272010938291607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-40570376630134265046163099369164400000000000000)
      constant := (91232007758866623511036803982205631434705704894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2462395225863724861/1562500000000000000)
  centralHi := (31518658891055678221/20000000000000000000)
  directionLo := (8264262081849002987/5000000000000000000)
  directionHi := (165285241636980059741/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree012.table
  base := (8251197078546194060032122182052863146541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-10482603756435318682616042270300000000000000)
      constant := (21148324483232064496603168590830369647614629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree012.table
  base := (6361105751761750093534075106070524297/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-47033370205312574381426581636845400000000000000)
      constant := (94035440890644292623505702757651550018919842500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8264262081849002987/5000000000000000000)
  centralHi := (165285241636980059741/100000000000000000000)
  directionLo := (172634804569419589179/100000000000000000000)
  directionHi := (8631740228470979459/5000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree013.table
  base := (286495768582732121687929820041671240597/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-11931877486870628317094933177300000000000000)
      constant := (22845962544554301928276422372140958567545860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree013.table
  base := (2725580973362527528959923537377215409507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-53496363780490883716690063904526400000000000000)
      constant := (102224955923849262225579609431778338165654873388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172634804569419589179/100000000000000000000)
  centralHi := (8631740228470979459/5000000000000000000)
  directionLo := (701890630852815093/390625000000000000)
  directionHi := (179684001498320663809/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree014.table
  base := (1763747678348486569897921437671790233381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-13381151217305937951573824084300000000000000)
      constant := (25646004786928625996832884058545361658997178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree014.table
  base := (1633167615069074598275044771305095579541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-59959357355669193051953546172207400000000000000)
      constant := (115319404614761325476341163282443347796388433844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (701890630852815093/390625000000000000)
  centralHi := (179684001498320663809/100000000000000000000)
  directionLo := (46616725163946865379/25000000000000000000)
  directionHi := (186466900655787461517/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree015.table
  base := (794183645142682155927748146634130868791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-14830424947741247586052714991300000000000000)
      constant := (29472376231657108567323781537484250318749758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree015.table
  base := (1342682852235997642552513806572676687643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-66422350930847502387217028439888400000000000000)
      constant := (132990856195094360635204798767719989194623273606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46616725163946865379/25000000000000000000)
  centralHi := (186466900655787461517/100000000000000000000)
  directionLo := (96505789574903378351/50000000000000000000)
  directionHi := (193011579149806756703/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree016.table
  base := (-25433725423129246912273002158280414731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-16279698678176557220531605898300000000000000)
      constant := (34270727853175701909170091049026570561166305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree016.table
  base := (-358702848555863870537535329129970184449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-72885344506025811722480510707569400000000000000)
      constant := (155003987711991906798239796817022690871667811342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96505789574903378351/50000000000000000000)
  centralHi := (193011579149806756703/100000000000000000000)
  directionLo := (199341501779305671567/100000000000000000000)
  directionHi := (12458843861206604473/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree017.table
  base := (-412224699881522604705999928721384784471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-17728972408611866855010496805300000000000000)
      constant := (40000282064380982324755297462921696920236804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree017.table
  base := (-1867162765822775896772546575964603746203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-79348338081204121057743992975250400000000000000)
      constant := (181181338340553576642122625001131743108857674874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199341501779305671567/100000000000000000000)
  centralHi := (12458843861206604473/6250000000000000000)
  directionLo := (51369129212833006539/25000000000000000000)
  directionHi := (205476516851332026157/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree018.table
  base := (-1500084726563547685893666876196853616459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-19178246139047176489489387712300000000000000)
      constant := (46629077881630986771939007176373014798135258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree018.table
  base := (-400725765148830154005265474737221527639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-85811331656382430393007475242931400000000000000)
      constant := (211383137915954276588836353866642382345837114896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51369129212833006539/25000000000000000000)
  centralHi := (205476516851332026157/100000000000000000000)
  directionLo := (1651824933750671127/781250000000000000)
  directionHi := (211433591520085904257/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree019.table
  base := (-4199945997351122324511679720733608058873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-20627519869482486123968278619300000000000000)
      constant := (54131151659412675825399652243515690567402863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree019.table
  base := (-4393482362547109720801806339125442534579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-92274325231560739728270957510612400000000000000)
      constant := (245495380415803111567851523219336105193772839882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1651824933750671127/781250000000000000)
  centralHi := (211433591520085904257/100000000000000000000)
  directionLo := (54306841344351674309/25000000000000000000)
  directionHi := (217227365377406697237/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree020.table
  base := (-5264063030524826481447796583727201044519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-22076793599917795758447169526300000000000000)
      constant := (62484825832616858510244143642877461770053489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree020.table
  base := (-5445977222576135161023063073810159850889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-98737318806739049063534439778293400000000000000)
      constant := (283422589908680219492217580212810291163139412862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54306841344351674309/25000000000000000000)
  centralHi := (217227365377406697237/100000000000000000000)
  directionLo := (222870574357711381071/100000000000000000000)
  directionHi := (13929410897356961317/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree021.table
  base := (-48484431518835711097056373920877017317/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-23526067330353105392926060433300000000000000)
      constant := (71671637133910312036026590722896878501507456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree021.table
  base := (-6376763208984641245216218396325472019151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-105200312381917358398797922045974400000000000000)
      constant := (325083281407627260794098495411390284463946117458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222870574357711381071/100000000000000000000)
  centralHi := (13929410897356961317/6250000000000000000)
  directionLo := (114187190131230313137/50000000000000000000)
  directionHi := (9134975210498425051/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree022.table
  base := (-1759356852711254407257360239834075639389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-24975341060788415027404951340300000000000000)
      constant := (81675638353580289352434225323268601798705836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree022.table
  base := (-7197490759033372817386501741133161050103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-111663305957095667734061404313655400000000000000)
      constant := (370406990248685433556698391929928087744002931074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114187190131230313137/50000000000000000000)
  centralHi := (9134975210498425051/4000000000000000000)
  directionLo := (233748630383131386503/100000000000000000000)
  directionHi := (29218578797891423313/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree023.table
  base := (-1942120584932840080859425415378534212127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-26424614791223724661883842247300000000000000)
      constant := (92482922121937675051328633867787146654392548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree023.table
  base := (-989790690288472857494582156063956760879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-118126299532273977069324886581336400000000000000)
      constant := (419332232123074718462702766903937826261341402256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233748630383131386503/100000000000000000000)
  centralHi := (29218578797891423313/12500000000000000000)
  directionLo := (239002064534423177953/100000000000000000000)
  directionHi := (119501032267211588977/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree024.table
  base := (-420404494341296269908593587489586009277/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-27873888521659034296362733154300000000000000)
      constant := (104081279880762606035506633149735135065995740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree024.table
  base := (-8548191886292282900427728597314841475847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-124589293107452286404588368849017400000000000000)
      constant := (471805030175587623366195652911140888562440189026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239002064534423177953/100000000000000000000)
  centralHi := (119501032267211588977/50000000000000000000)
  directionLo := (244142481959701944321/100000000000000000000)
  directionHi := (122071240979850972161/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree025.table
  base := (-896411402750033316118603121805459750479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-29323162252094343930841624061300000000000000)
      constant := (116459945847771334103379087657483256015942490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree025.table
  base := (-909495734569784349771789147396047412249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-131052286682630595739851851116698400000000000000)
      constant := (527777799894278478271964665201566604072442837420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244142481959701944321/100000000000000000000)
  centralHi := (122071240979850972161/50000000000000000000)
  directionLo := (249176877224132089459/100000000000000000000)
  directionHi := (12458843861206604473/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree026.table
  base := (-472175562676969871504102035435105839949/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-30772435982529653565320514968300000000000000)
      constant := (129609396585710449138649050171586802102196380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree026.table
  base := (-478278895906643640977561492086956627323/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-137515280257808905075115333384379400000000000000)
      constant := (587208469601295369346837954736914425488933676680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249176877224132089459/100000000000000000000)
  centralHi := (12458843861206604473/5000000000000000000)
  directionLo := (254111551860392614291/100000000000000000000)
  directionHi := (63527887965098153573/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree027.table
  base := (-9852449162096104364124378808197319391157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-32221709712964963199799405875300000000000000)
      constant := (143521188654077513089283449507177869753506067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree027.table
  base := (-2491554161195207558835009973843879434231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-143978273832987214410378815652060400000000000000)
      constant := (650059763732104767927442556355810237851791312392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254111551860392614291/100000000000000000000)
  centralHi := (63527887965098153573/25000000000000000000)
  directionLo := (32369025856766172971/12500000000000000000)
  directionHi := (258952206854129383769/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree028.table
  base := (-10196405051744973880035089802490250340421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-33670983443400272834278296782300000000000000)
      constant := (158187823631124008189289807036790847283963651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree028.table
  base := (-1030234255273008288619938890888567157227/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-150441267408165523745642297919741400000000000000)
      constant := (716298604287371674159466393338724707998390550660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32369025856766172971/12500000000000000000)
  centralHi := (258952206854129383769/100000000000000000000)
  directionLo := (52740803968218239853/20000000000000000000)
  directionHi := (131852009920545599633/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree029.table
  base := (-10480249469476600000592807643527563061191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-35120257173835582468757187689300000000000000)
      constant := (173602633738019811221484172880210766169229521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree029.table
  base := (-10578814765022631111533220732529555282461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-156904260983343833080905780187422400000000000000)
      constant := (785895602115030293826112277524873827499297516438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52740803968218239853/20000000000000000000)
  centralHi := (131852009920545599633/50000000000000000000)
  directionLo := (268371709995814254751/100000000000000000000)
  directionHi := (8386615937369195461/3125000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree030.table
  base := (-2677079490243315363678641953707013367847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-36569530904270892103236078596300000000000000)
      constant := (189759683612725882605979125460500394797669828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree030.table
  base := (-10799954867559954169786123297349792956387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-163367254558522142416169262455103400000000000000)
      constant := (858824619217724692214326797517032493549875978346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268371709995814254751/100000000000000000000)
  centralHi := (8386615937369195461/3125000000000000000)
  directionLo := (5459191858574096191/2000000000000000000)
  directionHi := (272959592928704809551/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree031.table
  base := (-10884473264157962648934004089392535039089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-38018804634706201737714969503300000000000000)
      constant := (206653685167025629310230120142421619531487159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree031.table
  base := (-5484804848725472459666756988822605336063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-169830248133700451751432744722784400000000000000)
      constant := (935062388993685704964583702184436825713999297508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5459191858574096191/2000000000000000000)
  centralHi := (272959592928704809551/100000000000000000000)
  directionLo := (27747162740995888093/10000000000000000000)
  directionHi := (277471627409958880931/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree032.table
  base := (-11012159564031481971628860270224069663667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-39468078365141511372193860410300000000000000)
      constant := (224279923311652985720548025659663248630439877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree032.table
  base := (-11091206134741790966857969643598609058341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-176293241708878761086696226990465400000000000000)
      constant := (1014588184843089018254265949432618661551761513478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27747162740995888093/10000000000000000000)
  centralHi := (277471627409958880931/100000000000000000000)
  directionLo := (550608311250223709/195312500000000000)
  directionHi := (281911455360114539009/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree033.table
  base := (-2773612507867450006199352159918333669643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-40917352095576821006672751317300000000000000)
      constant := (242634190875678734392797207257687204825034932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree033.table
  base := (-2233559821270625562321876899150771903721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-182756235284057070421959709258146400000000000000)
      constant := (1097383529828626313790119360662292135197473457590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550608311250223709/195312500000000000)
  centralHi := (281911455360114539009/100000000000000000000)
  directionLo := (286282436256548334439/100000000000000000000)
  directionHi := (7157060906413708361/2500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree034.table
  base := (-11134088606810712444781616365115881151483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-42366625826012130641151642224300000000000000)
      constant := (261712731404780433100825511884356358703619773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree034.table
  base := (-11202113761289644578377307016428375838099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-189219228859235379757223191525827400000000000000)
      constant := (1183431941589631172610648547581668807264224428042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286282436256548334439/100000000000000000000)
  centralHi := (7157060906413708361/2500000000000000000)
  directionLo := (290587676880337560237/100000000000000000000)
  directionHi := (145293838440168780119/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree035.table
  base := (-11133526807472369008978430067274185830147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-43815899556447440275630533131300000000000000)
      constant := (281512188771612634799376519615901639598528757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree035.table
  base := (-11196582600762389953844317849007529990479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-195682222434413689092486673793508400000000000000)
      constant := (1272718707770113879185015085275038248795325312082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290587676880337560237/100000000000000000000)
  centralHi := (145293838440168780119/50000000000000000000)
  directionLo := (73707514288079151429/25000000000000000000)
  directionHi := (294830057152316605717/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree036.table
  base := (-11094956206857777317539967279983699168839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-45265173286882749910109424038300000000000000)
      constant := (302029562712186622083841981548502315837859409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree036.table
  base := (-11153378217648640342958937739148571679431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-202145216009591998427750156061189400000000000000)
      constant := (1365230688002585189515200322730644964528454889698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73707514288079151429/25000000000000000000)
  centralHi := (294830057152316605717/100000000000000000000)
  directionLo := (299012252668958507351/100000000000000000000)
  directionHi := (37376531583619813419/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree037.table
  base := (-5510168565779515840653230087947085891399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1820)
      previous := (1547)
      next := (0)
      square := (42625697953979695131732085500000000000000)
      linear := (-1262552622089677284988873376900000000000000)
      constant := (8736815392956697779531935671291915644036474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree037.table
  base := (-11074442200364269878047612559524149257103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1634660000000000000000000000000000000000000000
      center := (7976605)
      previous := (6898801)
      next := (0)
      square := (188320333560682293091992353739000000000000000)
      linear := (-5638059718507305615216584819699200000000000000)
      constant := (39485301056498418924523078170558475417538401002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299012252668958507351/100000000000000000000)
  centralHi := (37376531583619813419/12500000000000000000)
  directionLo := (303136754439134107273/100000000000000000000)
  directionHi := (151568377219567053637/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree038.table
  base := (-5455712022414433391279160816466550525109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-48163720747753369179067205852300000000000000)
      constant := (345207607393053228295853549253914584662251558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree038.table
  base := (-2192302135413402304314338599070200434347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-215071203159948617098277120596551400000000000000)
      constant := (1559884560510441828133132629424037463922821160130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303136754439134107273/100000000000000000000)
  centralHi := (151568377219567053637/50000000000000000000)
  directionLo := (307205886235304254107/100000000000000000000)
  directionHi := (76801471558826063527/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree039.table
  base := (-10769788020056892756055452249882598820029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-49612994478188678813546096759300000000000000)
      constant := (367863725473682477168871465877110722215380299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree039.table
  base := (-338004278477394071709527278803271127711/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-221534196735126926433540602864232400000000000000)
      constant := (1662006557748928983626182909480391916495710910016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307205886235304254107/100000000000000000000)
  centralHi := (76801471558826063527/25000000000000000000)
  directionLo := (311221819902373663357/100000000000000000000)
  directionHi := (155610909951186831679/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree040.table
  base := (-5298418327302755891084857628785913387041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-51062268208623988448024987666300000000000000)
      constant := (391228596780496435876806288944384169146281742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree040.table
  base := (-10639711305808917997891893670487958927177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-227997190310305235768804085131913400000000000000)
      constant := (1767313721313195213561279229276976566322373127166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311221819902373663357/100000000000000000000)
  centralHi := (155610909951186831679/50000000000000000000)
  directionLo := (315186588910556782209/100000000000000000000)
  directionHi := (31518658891055678221/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree041.table
  base := (-10393831729265525791100179524005731742543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-52511541939059298082503878573300000000000000)
      constant := (415300493935592496577215493175436153244458633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree041.table
  base := (-10433479125971942422894570825633386940369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-234460183885483545104067567399594400000000000000)
      constant := (1875798519537303482275960521802796122505008718702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315186588910556782209/100000000000000000000)
  centralHi := (31518658891055678221/10000000000000000000)
  directionLo := (319102100392333869463/100000000000000000000)
  directionHi := (39887762549041733683/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree042.table
  base := (-5080952440029627131577197937565395170171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-53960815669494607716982769480300000000000000)
      constant := (440077867729256103901558041489545948024071802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree042.table
  base := (-2549639053404887916015482785880691378037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-240923177460661854439331049667275400000000000000)
      constant := (1987454203539687866899525040770778381673274956184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319102100392333869463/100000000000000000000)
  centralHi := (39887762549041733683/12500000000000000000)
  directionLo := (80742536466430571929/25000000000000000000)
  directionHi := (322970145865722287717/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree043.table
  base := (-9902071515933208660469707505877426343317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-55410089399929917351461660387300000000000000)
      constant := (465559328066639483658167911052853803335999027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree043.table
  base := (-9935942929724786337689839221657049987561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-247386171035840163774594531934956400000000000000)
      constant := (2102274722895096062308786253496004970669134082238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80742536466430571929/25000000000000000000)
  centralHi := (322970145865722287717/100000000000000000000)
  directionLo := (326792410814958705071/100000000000000000000)
  directionHi := (20424525675934919067/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree044.table
  base := (-1923048637429035695699544959364807833891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-56859363130365226985940551294300000000000000)
      constant := (491743627035439722027771847254347890377016105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree044.table
  base := (-9646536533735898731267645613894347303147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-253849164611018473109858014202637400000000000000)
      constant := (2220254650761248252191954995405908025078519582426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326792410814958705071/100000000000000000000)
  centralHi := (20424525675934919067/6250000000000000000)
  directionLo := (330570483273960119481/100000000000000000000)
  directionHi := (165285241636980059741/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree045.table
  base := (-2325559646042883641560308449666039716577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-58308636860800536620419442201300000000000000)
      constant := (518629643848394667318085035990628766512024348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree045.table
  base := (-9331142182425169540804748798099343705107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-260312158186196782445121496470318400000000000000)
      constant := (2341389117355137744007637990231930279230336228106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330570483273960119481/100000000000000000000)
  centralHi := (165285241636980059741/50000000000000000000)
  directionLo := (334305861536567071607/100000000000000000000)
  directionHi := (41788232692070883951/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree046.table
  base := (-4481896662595132896063494747947710572837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-59757910591235846254898333108300000000000000)
      constant := (546216371444218652768231249687919168451572294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree046.table
  base := (-4495241354339332893027748611823113781549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-266775151761375091780384978737999400000000000000)
      constant := (2465673750808544045992142157999931893311313026284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334305861536567071607/100000000000000000000)
  centralHi := (41788232692070883951/12500000000000000000)
  directionLo := (4224999513746887013/1250000000000000000)
  directionHi := (337999961099750961041/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree047.table
  base := (-8600568671184810242216392156961948004169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-61207184321671155889377224015300000000000000)
      constant := (574502904556625351638392431378719093182292639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree047.table
  base := (-4312603660623697308549031551687902554957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1286860000000000000000000000000000000000000000
      center := (6279455)
      previous := (5430971)
      next := (0)
      square := (148252177483941379668164193369000000000000000)
      linear := (-5813577560352200023737201297993200000000000000)
      constant := (55172438820209203173575838175510131143625606996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4224999513746887013/1250000000000000000)
  centralHi := (337999961099750961041/100000000000000000000)
  directionLo := (170827060465518731279/50000000000000000000)
  directionHi := (341654120931037462559/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree048.table
  base := (-102664491138612403313488377257638367329/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-62656458052106465523856114922300000000000000)
      constant := (603488429083844358395376759785143446010127920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree048.table
  base := (-1029487418687959863974416813886824755653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-279701138911731710450911943273361400000000000000)
      constant := (2723678210461793736637953509089767386129758303792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170827060465518731279/50000000000000000000)
  centralHi := (341654120931037462559/100000000000000000000)
  directionLo := (172634804569419589179/50000000000000000000)
  directionHi := (345269609138839178359/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree049.table
  base := (-1560420036967625124692999140467948152231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-64105731782541775158335005829300000000000000)
      constant := (633172212610964228497979523053696894897978805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree049.table
  base := (-977885392799501323498042142363643188457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-286164132486910019786175425541042400000000000000)
      constant := (2857391337155094683777687054576227721956483659248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172634804569419589179/50000000000000000000)
  centralHi := (345269609138839178359/100000000000000000000)
  directionLo := (348847628113784925243/100000000000000000000)
  directionHi := (87211907028446231311/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree050.table
  base := (-3683936429717856102990896571241550040611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-65555005512977084792813896736300000000000000)
      constant := (663553595954897167860696883352940635988807082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree050.table
  base := (-923403777224136667328940313179458491503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-292627126062088329121438907808723400000000000000)
      constant := (2994241152775558146415910234042498764915479298192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348847628113784925243/100000000000000000000)
  centralHi := (87211907028446231311/25000000000000000000)
  directionLo := (352389319200143173761/100000000000000000000)
  directionHi := (176194659600071586881/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree051.table
  base := (-6910910841957261067893296960292120738367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-67004279243412394427292787643300000000000000)
      constant := (694631985617076804586872651308160086709175577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree051.table
  base := (-692876474701408729890106568315108763389/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-299090119637266638456702390076404400000000000000)
      constant := (3134225091832396384818397406919872549427025878620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352389319200143173761/100000000000000000000)
  centralHi := (176194659600071586881/50000000000000000000)
  directionLo := (355895766948789659719/100000000000000000000)
  directionHi := (8897394173719741493/2500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree052.table
  base := (-6431604603592395957714998673567928541481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-68453552973847704061771678550300000000000000)
      constant := (726406847042444543764789119031485505826712511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree052.table
  base := (-806008556168832802640116421450024772167/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-305553113212444947791965872344085400000000000000)
      constant := (3277340845594957310529340579338044874175512956688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355895766948789659719/100000000000000000000)
  centralHi := (8897394173719741493/2500000000000000000)
  directionLo := (359368002996641327617/100000000000000000000)
  directionHi := (179684001498320663809/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree053.table
  base := (-5930305960200259112523152223745836074843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-69902826704283013696250569457300000000000000)
      constant := (758877698595089219671888894877091950413539933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree053.table
  base := (-5945484962618504875587714336217016217883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-312016106787623257127229354611766400000000000000)
      constant := (3423586335658571302194732734379737571396318888314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359368002996641327617/100000000000000000000)
  centralHi := (179684001498320663809/50000000000000000000)
  directionLo := (181403504805944156071/50000000000000000000)
  directionHi := (362807009611888312143/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree054.table
  base := (-216293280290831898666722071663794289581/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-71352100434718323330729460364300000000000000)
      constant := (792044106171285094955046426111506640439090275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree054.table
  base := (-1084264749615248854966295801452123497903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-318479100362801566462492836879447400000000000000)
      constant := (3572959690326656543329625810095151628353980817370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181403504805944156071/50000000000000000000)
  centralHi := (362807009611888312143/100000000000000000000)
  directionLo := (366213722939552916481/100000000000000000000)
  directionHi := (183106861469776458241/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree055.table
  base := (-1215742160128759012926909143034346504867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-72801374165153632965208351271300000000000000)
      constant := (825905678379803776346058893976743918539348308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree055.table
  base := (-243793179064179425471666447155026768963/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-324942093937979875797756319147128400000000000000)
      constant := (3725459223497164235162475771536206981696673739080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366213722939552916481/100000000000000000000)
  centralHi := (183106861469776458241/50000000000000000000)
  directionLo := (23099314748610376957/6250000000000000000)
  directionHi := (369589035977766031313/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree056.table
  base := (-4297473707437055776021875488580716741463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-74250647895588942599687242178300000000000000)
      constant := (860462062227412177081354121016932998780937153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree056.table
  base := (-4309355674520545291166532162326714897981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-331405087513158185133019801414809400000000000000)
      constant := (3881083415777431519290611644595611145232005600598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23099314748610376957/6250000000000000000)
  centralHi := (369589035977766031313/100000000000000000000)
  directionLo := (46616725163946865379/12500000000000000000)
  directionHi := (372933801311574923033/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree057.table
  base := (-3711079830069912469467473007853235389931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-75699921626024252234166133085300000000000000)
      constant := (895712939254547043729858278816848920751184461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree057.table
  base := (-372202647115394315585292064377643158351/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-337868081088336494468283283682490400000000000000)
      constant := (4039830897583176521956877320582017397886488310580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46616725163946865379/12500000000000000000)
  centralHi := (372933801311574923033/100000000000000000000)
  directionLo := (376248833627996845211/100000000000000000000)
  directionHi := (94062208406999211303/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree058.table
  base := (-3103996934500678186867182148727946477359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-77149195356459561868645023992300000000000000)
      constant := (931658022072395174648519018493791441272495529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree058.table
  base := (-3114080147727163935660838396297330262569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-344331074663514803803546765950171400000000000000)
      constant := (4201700434005254146341915270190665042618059146302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376248833627996845211/100000000000000000000)
  centralHi := (94062208406999211303/25000000000000000000)
  directionLo := (18976745601666981927/5000000000000000000)
  directionHi := (379534912033339638541/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree059.table
  base := (-1238207259395347885474184702352276614043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-78598469086894871503123914899300000000000000)
      constant := (968297051258110591485642575318159466630750266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree059.table
  base := (-497140171097319288090044369735419894023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-350794068238693113138810248217852400000000000000)
      constant := (4366690911252361631297600611795630372546672712170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18976745601666981927/5000000000000000000)
  centralHi := (379534912033339638541/100000000000000000000)
  directionLo := (382792782191464087497/100000000000000000000)
  directionHi := (191396391095732043749/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree060.table
  base := (-57140740229691642811719047532909933107/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-80047742817330181137602805806300000000000000)
      constant := (1005629792569755775141455567863678281650448544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree060.table
  base := (-459263682369063165759259405415992530359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-357257061813871422474073730485533400000000000000)
      constant := (4534801324499548111640480117810705866024785684488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382792782191464087497/100000000000000000000)
  centralHi := (191396391095732043749/50000000000000000000)
  directionLo := (77204631659922702681/20000000000000000000)
  directionHi := (193011579149806756703/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree061.table
  base := (-1160418976693445604936589894421089841377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-81497016547765490772081696713300000000000000)
      constant := (1043656034446842433954223387884337528007154887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree061.table
  base := (-584145845085645188453911680068318539179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-363720055389049731809337212753214400000000000000)
      constant := (4706030766991499078168326024817555115883917853364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77204631659922702681/20000000000000000000)
  centralHi := (193011579149806756703/50000000000000000000)
  directionLo := (389226724916641972901/100000000000000000000)
  directionHi := (194613362458320986451/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree062.table
  base := (-472299994734120959229084830169220130999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-82946290278200800406560587620300000000000000)
      constant := (1082375585766137005475776946556098337640662369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree062.table
  base := (-47954705983037338388400429346244577859/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-370183048964228041144600695020895400000000000000)
      constant := (4880378420266446145611082312244058910019209261220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389226724916641972901/100000000000000000000)
  centralHi := (194613362458320986451/50000000000000000000)
  directionLo := (98101034664224518411/25000000000000000000)
  directionHi := (78480827731379614729/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree063.table
  base := (11786355333548703580224419242467317489/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-84395564008636110041039478527300000000000000)
      constant := (1121788273825747438378517853213258755152848820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree063.table
  base := (114528493359555322198690169966410179139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-376646042539406350479864177288576400000000000000)
      constant := (5057843545381466965102871630612722411269392047276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98101034664224518411/25000000000000000000)
  centralHi := (78480827731379614729/20000000000000000000)
  directionLo := (197778014880818399449/50000000000000000000)
  directionHi := (395556029761636798899/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree064.table
  base := (481774154191794828932880783928656007729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-85844837739071419675518369434300000000000000)
      constant := (1161893942533473468645589041813596660149162002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree064.table
  base := (478705059664644938745102981552686573077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-383109036114584659815127659556257400000000000000)
      constant := (5238425475033127312028172850520041968288240761268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197778014880818399449/50000000000000000000)
  centralHi := (395556029761636798899/100000000000000000000)
  directionLo := (79736600711722268627/20000000000000000000)
  directionHi := (12458843861206604473/3125000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree065.table
  base := (1711060534226699836546981657222718395493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-87294111469506729309997260341300000000000000)
      constant := (1202692450778028747733632898415737901483429917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree065.table
  base := (426353170552244550910894657707042849911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-389572029689762969150391141823938400000000000000)
      constant := (5422123606479085391316077521668949691042525625848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79736600711722268627/20000000000000000000)
  centralHi := (12458843861206604473/3125000000000000000)
  directionLo := (200892820909709534089/50000000000000000000)
  directionHi := (401785641819419068179/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree066.table
  base := (495634116176358880758673837069861469191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-88743385199942038944476151248300000000000000)
      constant := (1244183670964070235173572229928543201756612395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree066.table
  base := (494594928426666991623642001593951664539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-396035023264941278485654624091619400000000000000)
      constant := (5608937395176609326214801561300793427017173452190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200892820909709534089/50000000000000000000)
  centralHi := (401785641819419068179/100000000000000000000)
  directionLo := (404864504023221725399/100000000000000000000)
  directionHi := (2024322520116108627/500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree067.table
  base := (1632397077511087340565882870432705598509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-90192658930377348578955042155300000000000000)
      constant := (1286367487694033680474577282486844747928717642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree067.table
  base := (3260014642802958013880602127551712897381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-402498016840119587820918106359300400000000000000)
      constant := (5798866349063112108204731631604779677117881454202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404864504023221725399/100000000000000000000)
  centralHi := (2024322520116108627/500000000000000000)
  directionLo := (203960064267307074557/50000000000000000000)
  directionHi := (81584025706922829823/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree068.table
  base := (2035427503300471503290477767937100934209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-91641932660812658213433933062300000000000000)
      constant := (1329243796581604880737395771677011782357864242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree068.table
  base := (813291830862228041193957625576838711869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-408961010415297897156181588626981400000000000000)
      constant := (5991910023411923734929049884447427750621759921490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203960064267307074557/50000000000000000000)
  centralHi := (81584025706922829823/20000000000000000000)
  directionLo := (410953033702664052313/100000000000000000000)
  directionHi := (205476516851332026157/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree069.table
  base := (2448142074199905528089923243123092077559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-93091206391247967847912823969300000000000000)
      constant := (1372812503183281999246524962435871026108356542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree069.table
  base := (2446120853934234376681903549660740059/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-415424003990476206491445070894662400000000000000)
      constant := (6188068016203720390850242492932660197551852556000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410953033702664052313/100000000000000000000)
  centralHi := (205476516851332026157/50000000000000000000)
  directionLo := (413963718887476592273/100000000000000000000)
  directionHi := (206981859443738296137/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree070.table
  base := (2870509576499928237658229784535796841153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-94540480121683277482391714876300000000000000)
      constant := (1417073522035928531298501055481059011751076914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree070.table
  base := (2868651103495418601095828647034997408763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-421886997565654515826708553162343400000000000000)
      constant := (6387339963960422850981535801707398493595143089292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413963718887476592273/100000000000000000000)
  centralHi := (206981859443738296137/50000000000000000000)
  directionLo := (416952665420040878083/100000000000000000000)
  directionHi := (104238166355010219521/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree071.table
  base := (6605003519273313757190879044335166929327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-95989753852118587116870605783300000000000000)
      constant := (1462026775789500565914514966164494843526248663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree071.table
  base := (1650396576823969294647470841955478480739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-428349991140832825161972035430024400000000000000)
      constant := (6589725537994055210864657157893075598309207243352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416952665420040878083/100000000000000000000)
  centralHi := (104238166355010219521/25000000000000000000)
  directionLo := (209960168750291396857/50000000000000000000)
  directionHi := (83984067500116558743/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree072.table
  base := (7488186101329920292229442156270678855703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-97439027582553896751349496690300000000000000)
      constant := (1507672194425274333582060350173534559353457407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree072.table
  base := (1497008971577503008481951709527056502751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-434812984716011134497235517697705400000000000000)
      constant := (6795224441028103500274166145975059516381558568710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209960168750291396857/50000000000000000000)
  centralHi := (83984067500116558743/20000000000000000000)
  directionLo := (422867183040171808513/100000000000000000000)
  directionHi := (211433591520085904257/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree073.table
  base := (1678104118718830721332175962466643136949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-98888301312989206385828387597300000000000000)
      constant := (1554009714550916944034544340120484172272415905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree073.table
  base := (8387633398050871049497056004775742070919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-441275978291189443832498999965386400000000000000)
      constant := (7003836404153404633516519916770272293774499274398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422867183040171808513/100000000000000000000)
  centralHi := (211433591520085904257/50000000000000000000)
  directionLo := (425793634449902240309/100000000000000000000)
  directionHi := (42579363444990224031/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree074.table
  base := (9311965066351369675445663361676868320429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1820)
      previous := (1547)
      next := (0)
      square := (42625697953979695131732085500000000000000)
      linear := (-2711826352524986919467764283900000000000000)
      constant := (43271331858504028367613184358982044127855873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree074.table
  base := (4654655851820325230126676522984912920007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1634660000000000000000000000000000000000000000
      center := (7976605)
      previous := (6898801)
      next := (0)
      square := (188320333560682293091992353739000000000000000)
      linear := (-12101053293685614950480067087380200000000000000)
      constant := (195015167137421449320143249378689303550763728524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425793634449902240309/100000000000000000000)
  centralHi := (42579363444990224031/10000000000000000000)
  directionLo := (428700109381585980233/100000000000000000000)
  directionHi := (214350054690792990117/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree075.table
  base := (410099261867624668853415644968923305609/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-101786848773859825654786169411300000000000000)
      constant := (1648760835081555557300437731759061400134468025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree075.table
  base := (5125021689067431192138512135739682475609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-454201965441546062503025964500748400000000000000)
      constant := (7430398560686697515033562569087792147231284658756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428700109381585980233/100000000000000000000)
  centralHi := (214350054690792990117/50000000000000000000)
  directionLo := (431587011423548972947/100000000000000000000)
  directionHi := (107896752855887243237/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree076.table
  base := (5606017820148946451456609753665473869337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-103236122504295135289265060318300000000000000)
      constant := (1697174336415820598609894412672336067454244706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree076.table
  base := (11209795483850366341473752058544252098817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-460664959016724371838289446768429400000000000000)
      constant := (7648348334744637751137700327191818204402653129714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431587011423548972947/100000000000000000000)
  centralHi := (107896752855887243237/25000000000000000000)
  directionLo := (54306841344351674309/12500000000000000000)
  directionHi := (434454730754813394473/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree077.table
  base := (12190596190023019652217058230107228924443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-104685396234730444923743951225300000000000000)
      constant := (1746279740113305579070517762427616796397562467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree077.table
  base := (12188538209284637332608425892108156002913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-467127952591902681173552929036110400000000000000)
      constant := (7869410325951232678351289738031777067679370528946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54306841344351674309/12500000000000000000)
  centralHi := (434454730754813394473/100000000000000000000)
  directionLo := (218651822380333825249/50000000000000000000)
  directionHi := (437303644760667650499/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree078.table
  base := (1318813496756245334598239653691856864033/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-106134669965165754558222842132300000000000000)
      constant := (1796077007529462947462058665800441520468611770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree078.table
  base := (13186244568965651754053005831577795371333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-473590946167080990508816411303791400000000000000)
      constant := (8093584371091817013689876338061294948232301846586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218651822380333825249/50000000000000000000)
  centralHi := (437303644760667650499/100000000000000000000)
  directionLo := (110033529653093417699/25000000000000000000)
  directionHi := (440134118612373670797/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree079.table
  base := (177557829937185692510288577713915571339/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-107583943695601064192701733039300000000000000)
      constant := (1846566103648091011263861485890428033373047280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree079.table
  base := (3550722533141143208451660854717685194309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-480053939742259299844079893571472400000000000000)
      constant := (8320870322405849812777900171600562456939991419112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110033529653093417699/25000000000000000000)
  centralHi := (440134118612373670797/100000000000000000000)
  directionLo := (442946505813532547871/100000000000000000000)
  directionHi := (13842078306672892121/3125000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree080.table
  base := (3048009458616206792089933811494130558527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-109033217426036373827180623946300000000000000)
      constant := (1897746996736893456824665954403677323673117315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree080.table
  base := (15238452780358940849692076220324605406633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-486516933317437609179343375839153400000000000000)
      constant := (8551268046107896666380380388553280532053824789186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442946505813532547871/100000000000000000000)
  centralHi := (13842078306672892121/3125000000000000000)
  directionLo := (222870574357711381071/50000000000000000000)
  directionHi := (445741148715422762143/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree081.table
  base := (8147188327049668448429760829643326159997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-110482491156471683461659514853300000000000000)
      constant := (1949619658036217202381236479907363427026071786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree081.table
  base := (8146456241215878457969151661908262763887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-492979926892615918514606858106834400000000000000)
      constant := (8784777421052172325322443618820709359991154873308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222870574357711381071/50000000000000000000)
  centralHi := (445741148715422762143/100000000000000000000)
  directionLo := (448518379003437761027/100000000000000000000)
  directionHi := (112129594750859440257/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree082.table
  base := (2170949429516948859223922921723999115771/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-111931764886906993096138405760300000000000000)
      constant := (2002184061477709124636231396573321238315923992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree082.table
  base := (4341562774814521853503595376171785426277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-499442920467794227849870340374515400000000000000)
      constant := (9021398337526440226045279033291848767320785820136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448518379003437761027/100000000000000000000)
  centralHi := (112129594750859440257/25000000000000000000)
  directionLo := (90255703631315898549/20000000000000000000)
  directionHi := (225639259078289746373/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree083.table
  base := (230746079717333462094195624863656192837/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-113381038617342302730617296667300000000000000)
      constant := (2055440183429960753783092256235467626239508240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree083.table
  base := (2307306525196132409461234536148427528819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-505905914042972537185133822642196400000000000000)
      constant := (9261130696162506341164946452504321950910074289584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90255703631315898549/20000000000000000000)
  centralHi := (225639259078289746373/50000000000000000000)
  directionLo := (227010938940904924173/50000000000000000000)
  directionHi := (454021877881809848347/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree084.table
  base := (19570633828131851937530552774812420158819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-114830312347777612365096187574300000000000000)
      constant := (2109388002468504392325489997501918203197423211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree084.table
  base := (19569500907596420157914534313177103603953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-512368907618150846520397304909877400000000000000)
      constant := (9503974406951834892593610925950494511455779900626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227010938940904924173/50000000000000000000)
  centralHi := (454021877881809848347/100000000000000000000)
  directionLo := (114187190131230313137/25000000000000000000)
  directionHi := (456748760524921252549/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree085.table
  base := (414008471975573276945919100673306191797/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-116279586078212921999575078481300000000000000)
      constant := (2164027499167787973562383313234087808828504650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree085.table
  base := (10349691867995955303424854604911596481493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-518831901193329155855660787177558400000000000000)
      constant := (9749929388355969120875668491451339698252836370612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114187190131230313137/25000000000000000000)
  centralHi := (456748760524921252549/100000000000000000000)
  directionLo := (459459459459459459459/100000000000000000000)
  directionHi := (22972972972972972973/5000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree086.table
  base := (4369808564480633206666622456975115465603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-117728859808648231634053969388300000000000000)
      constant := (2219358655912992614511442422237794665362052535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree086.table
  base := (10924044236443469946651823359940569180297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-525294894768507465190924269445239400000000000000)
      constant := (9998995566502476033082010954842415736040355775748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459459459459459459459/100000000000000000000)
  centralHi := (22972972972972972973/5000000000000000000)
  directionLo := (462154259455114703643/100000000000000000000)
  directionHi := (115538564863778675911/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree087.table
  base := (1438529989398701946563691239179724483107/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-119178133539083541268532860295300000000000000)
      constant := (2275381456729769146829664485836592685077975728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree087.table
  base := (1438475253231975340307271444450329576799/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-531757888343685774526187751712920400000000000000)
      constant := (10251172874458062748538582502430802454163806997728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462154259455114703643/100000000000000000000)
  centralHi := (115538564863778675911/25000000000000000000)
  directionLo := (232416718513445309303/50000000000000000000)
  directionHi := (464833437026890618607/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree088.table
  base := (24202724039830997154878080788723491172439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-120627407269518850903011751202300000000000000)
      constant := (2332095887130160515401435247634162459415068991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree088.table
  base := (24201920444529841309417162107337044800677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-538220881918864083861451233980601400000000000000)
      constant := (10506461251571345179838089876522499622519336259834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232416718513445309303/50000000000000000000)
  centralHi := (464833437026890618607/100000000000000000000)
  directionLo := (467497260766262773007/100000000000000000000)
  directionHi := (29218578797891423313/6250000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree089.table
  base := (25407765851767520614918391020757347568717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-122076680999954160537490642109300000000000000)
      constant := (2389501933973148118646453955129616808821573573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree089.table
  base := (1016281142550844269495175506957327604899/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-544683875494042393196714716248282400000000000000)
      constant := (10764860642878497504457138937276518875692738438950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467497260766262773007/100000000000000000000)
  centralHi := (29218578797891423313/6250000000000000000)
  directionLo := (117536497913862351399/25000000000000000000)
  directionHi := (470145991655449405597/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree090.table
  base := (13315798279435532311645781979638798674279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-123525954730389470171969533016300000000000000)
      constant := (2447599585338413974746090112357251030770175902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree090.table
  base := (5326184034670005670134597769694690454563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-551146869069220702531978198515963400000000000000)
      constant := (11026370998565682251544441749964044769921435141230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117536497913862351399/25000000000000000000)
  centralHi := (470145991655449405597/100000000000000000000)
  directionLo := (236389941682917586657/50000000000000000000)
  directionHi := (94555976673167034663/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree091.table
  base := (27874208262011441684758504968022690595189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-124975228460824779806448423923300000000000000)
      constant := (2506388830412048857019361398760023063424813741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree091.table
  base := (1393679390413256011251122541140685759673/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-557609862644399011867241680783644400000000000000)
      constant := (11290992273482763903870386326350838120409122897320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236389941682917586657/50000000000000000000)
  centralHi := (94555976673167034663/20000000000000000000)
  directionLo := (475399182541513756331/100000000000000000000)
  directionHi := (118849795635378439083/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree092.table
  base := (29135593794649651430330479718292256737527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-126424502191260089440927314830300000000000000)
      constant := (2565869659383060873961122237041942099473674463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree092.table
  base := (14567512350928655705035847394516100014651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-564072856219577321202505163051325400000000000000)
      constant := (11558724426703350868832049115635516491569625587084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475399182541513756331/100000000000000000000)
  centralHi := (118849795635378439083/25000000000000000000)
  directionLo := (478004129068846355907/100000000000000000000)
  directionHi := (119501032267211588977/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree093.table
  base := (30415746654375757837488759714669516165853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-127873775921695399075406205737300000000000000)
      constant := (2626042063349650823156544487892782567631052757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree093.table
  base := (30415224719989566522727162631451969585589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-570535849794755630537768645319006400000000000000)
      constant := (11829567421126697895269917569693401773430281984538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478004129068846355907/100000000000000000000)
  centralHi := (119501032267211588977/25000000000000000000)
  directionLo := (30037184770804369249/6250000000000000000)
  directionHi := (96118991266573981597/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree094.table
  base := (31714660940899483831059087966170629503967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-129323049652130708709885096644300000000000000)
      constant := (2686906034234321315289714593491887591790930823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree094.table
  base := (31714182301481334071106762727741890487039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1286860000000000000000000000000000000000000000
      center := (6279455)
      previous := (5430971)
      next := (0)
      square := (148252177483941379668164193369000000000000000)
      linear := (-12276571135530509359000683565674200000000000000)
      constant := (257521728151434876639736760913328992919215100754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30037184770804369249/6250000000000000000)
  centralHi := (96118991266573981597/20000000000000000000)
  directionLo := (241585945730665353601/50000000000000000000)
  directionHi := (483171891461330707203/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree095.table
  base := (1032260353121193914985441302901575124889/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-130772323382566018344363987551300000000000000)
      constant := (2748461564706977297924599001573512203071137312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree095.table
  base := (16515946202098369716672681569587837083737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-583461836945112249208295609854368400000000000000)
      constant := (12380585802179516822630480886007353407878031280708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241585945730665353601/50000000000000000000)
  centralHi := (483171891461330707203/100000000000000000000)
  directionLo := (485735155557065633989/100000000000000000000)
  directionHi := (48573515555706563399/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree096.table
  base := (3436875287202665375777461915050004433769/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-132221597113001327978842878458300000000000000)
      constant := (2810708648115257238587182090189834560698297610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree096.table
  base := (4296043807030513128054443346110487069947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-589924830520290558543559092122049400000000000000)
      constant := (12660761130661023493138376508539270276295283065392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485735155557065633989/100000000000000000000)
  centralHi := (48573515555706563399/10000000000000000000)
  directionLo := (244142481959701944321/50000000000000000000)
  directionHi := (488284963919403888643/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree097.table
  base := (8930980311751590087571601113469848449283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-133670870843436637613321769365300000000000000)
      constant := (2873647278421407773332152332553960890108273708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree097.table
  base := (35723552311797199072992845748677407697793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-596387824095468867878822574389730400000000000000)
      constant := (12944047183486998873889892693814181191688914929906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244142481959701944321/50000000000000000000)
  centralHi := (488284963919403888643/100000000000000000000)
  directionLo := (490821526255216688647/100000000000000000000)
  directionHi := (61352690781902086081/12500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree098.table
  base := (37097832421641292394907924161161195131297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-135120144573871947247800660272300000000000000)
      constant := (2937277450145080913445010562004029676134745593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree098.table
  base := (37097494211096185284903343410471717060849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-602850817670647177214086056657411400000000000000)
      constant := (13230443937917505613097845298255677478939543477458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490821526255216688647/100000000000000000000)
  centralHi := (61352690781902086081/12500000000000000000)
  directionLo := (98669009376040088653/20000000000000000000)
  directionHi := (246672523440100221633/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree099.table
  base := (38490482762049789269170104898703602561341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-136569418304307256882279551179300000000000000)
      constant := (3001599158311492665533596617091525231906475829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree099.table
  base := (153960690976916415216949399483708298933/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-609313811245825486549349538925092400000000000000)
      constant := (13519951373328570978859286422464368562338781446500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98669009376040088653/20000000000000000000)
  centralHi := (246672523440100221633/50000000000000000000)
  directionLo := (247927862455470089611/50000000000000000000)
  directionHi := (495855724910940179223/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree100.table
  base := (1995093448466113678320933717066466701943/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-138018692034742566516758442086300000000000000)
      constant := (3066612398404435818128200799003279858299199340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree100.table
  base := (7980316963666667640108483831317023821747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-615776804821003795884613021192773400000000000000)
      constant := (13812569471013813394249663503700852693968453593870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247927862455470089611/50000000000000000000)
  centralHi := (495855724910940179223/100000000000000000000)
  directionLo := (498353754448264178919/100000000000000000000)
  directionHi := (12458843861206604473/2500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree101.table
  base := (41331988048409731514502046530336221974141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-139467965765177876151237332993300000000000000)
      constant := (3132317166323688271374747586561830287882599029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree101.table
  base := (5166465953486417798614057130358286359201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-622239798396182105219876503460454400000000000000)
      constant := (14108298214004783805301311936820070350845972597136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498353754448264178919/100000000000000000000)
  centralHi := (12458843861206604473/2500000000000000000)
  directionLo := (62604915594045957469/12500000000000000000)
  directionHi := (500839324752367659753/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree102.table
  base := (21390418639960003836356782314374857351259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-140917239495613185785716223900300000000000000)
      constant := (3198713458346402164474909566557358359427747142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree102.table
  base := (42780598627826299332790804453634154871739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-628702791971360414555139985728135400000000000000)
      constant := (14407137586908241713987414201018051948129756432838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62604915594045957469/12500000000000000000)
  centralHi := (500839324752367659753/100000000000000000000)
  directionLo := (251656310205076322399/50000000000000000000)
  directionHi := (503312620410152644799/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree103.table
  base := (22124207097273945123646772535389397565757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-142366513226048495420195114807300000000000000)
      constant := (3265801271092098662483029732188296170535042666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree103.table
  base := (44248195509131704079902408994287366846369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-635165785546538723890403467995816400000000000000)
      constant := (14709087575758756998782412328849569062229616533298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251656310205076322399/50000000000000000000)
  centralHi := (503312620410152644799/100000000000000000000)
  directionLo := (20230952859808109891/4000000000000000000)
  directionHi := (126443455373800686819/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree104.table
  base := (45734716549891085553303286677727511647349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-143815786956483805054674005714300000000000000)
      constant := (3333580601490929025344427001541008963445220781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree104.table
  base := (45734516176794415514418537512894475235871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-641628779121717033225666950263497400000000000000)
      constant := (15014148167885183189037624111658317506689554888782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20230952859808109891/4000000000000000000)
  centralHi := (126443455373800686819/25000000000000000000)
  directionLo := (254111551860392614291/50000000000000000000)
  directionHi := (508223103720785228583/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree105.table
  base := (47239742309427772108226122057477877431661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-145265060686919114689152896621300000000000000)
      constant := (3402051446754894879449536056955687214203943909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree105.table
  base := (590494484122422259413142674085851780097/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-648091772696895342560930432531178400000000000000)
      constant := (15322319351789687329116927324054997077372595157920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254111551860392614291/50000000000000000000)
  centralHi := (508223103720785228583/100000000000000000000)
  directionLo := (510660638586248223813/100000000000000000000)
  directionHi := (255330319293124111907/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree106.table
  base := (48763489623452736969586960138043013312279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-146714334417354424323631787528300000000000000)
      constant := (3471213804351749788280108498754780885224509951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree106.table
  base := (24381660721490125773226627071236641892599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-654554766272073651896193914798859400000000000000)
      constant := (15633601117038147465017590225676947298867553521916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (510660638586248223813/100000000000000000000)
  centralHi := (255330319293124111907/50000000000000000000)
  directionLo := (256543296758579153209/50000000000000000000)
  directionHi := (513086593517158306419/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree107.table
  base := (25152978405894177074454150283312042469069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-148163608147789733958110678435300000000000000)
      constant := (3541067671981330581857918628955308372280310922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree107.table
  base := (25152901375327853080875177327581743492119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-661017759847251961231457397066540400000000000000)
      constant := (15947993454160842457553733302292423368844521609596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256543296758579153209/50000000000000000000)
  centralHi := (513086593517158306419/100000000000000000000)
  directionLo := (515501131999502445437/100000000000000000000)
  directionHi := (257750565999751222719/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree108.table
  base := (25933571174052034688143402959327945444949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-149612881878225043592589569342300000000000000)
      constant := (3611613047554090731387468778623039914628270362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree108.table
  base := (51867001231694663107171556589996795433073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-667480753422430270566720879334221400000000000000)
      constant := (16265496354562461482296603576405328598003720307666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (515501131999502445437/100000000000000000000)
  centralHi := (257750565999751222719/50000000000000000000)
  directionLo := (517904413708258767537/100000000000000000000)
  directionHi := (258952206854129383769/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree109.table
  base := (13361761211423447218904227655282557357547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-151062155608660353227068460249300000000000000)
      constant := (3682849929171629594489270428488527284089927372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree109.table
  base := (26723457798030452246407555732750040408829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-673943746997608579901984361601902400000000000000)
      constant := (16586109810440553304683345916976580989804753457236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517904413708258767537/100000000000000000000)
  centralHi := (258952206854129383769/50000000000000000000)
  directionLo := (130074148657655563929/25000000000000000000)
  directionHi := (520296594630622255717/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree110.table
  base := (11009132608914959116522380971548267419501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-152511429339095662861547351156300000000000000)
      constant := (3754778315109030831502315072813247890486484345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree110.table
  base := (6880693084073484799404125291576254966601/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-680406740572786889237247843869583400000000000000)
      constant := (16909833814711619196375381243078144011933638123536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130074148657655563929/25000000000000000000)
  centralHi := (520296594630622255717/100000000000000000000)
  directionLo := (3266736419900965571/625000000000000000)
  directionHi := (522677827184154491361/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree111.table
  base := (7082874474973085182166166921402748197643/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1820)
      previous := (1547)
      next := (0)
      square := (42625697953979695131732085500000000000000)
      linear := (-4161100082960296553946655190900000000000000)
      constant := (103443194697265970427565445759135213466502328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree111.table
  base := (28331443698951883306227261579454106472757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1634660000000000000000000000000000000000000000
      center := (7976605)
      previous := (6898801)
      next := (0)
      square := (188320333560682293091992353739000000000000000)
      linear := (-18564046868863924285743549355061200000000000000)
      constant := (465855901647138623375869887776083539937351391524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3266736419900965571/625000000000000000)
  centralHi := (522677827184154491361/100000000000000000000)
  directionLo := (262524130165055339659/50000000000000000000)
  directionHi := (525048260330110679319/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree112.table
  base := (29149521035382210791199218309173712696109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-155409976799966282130505132970300000000000000)
      constant := (3900709593816534512330209111284117625361946442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree112.table
  base := (58298942806393417368668998799608538290087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-693332727723143507907774808404945400000000000000)
      constant := (17566613443297808793471927021428370744844712377054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262524130165055339659/50000000000000000000)
  centralHi := (525048260330110679319/100000000000000000000)
  directionLo := (527408039682182398531/100000000000000000000)
  directionHi := (131852009920545599633/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree113.table
  base := (59953800911726243793342870073612251002689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-156859250530401591764984023877300000000000000)
      constant := (3974712483867328190940009819960175171622681241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree113.table
  base := (7494213752637446184454552678634012922981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-699795721298321817243038290672626400000000000000)
      constant := (17899669056468608642745921642806625366714531595216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527408039682182398531/100000000000000000000)
  centralHi := (131852009920545599633/25000000000000000000)
  directionLo := (16554915862840022259/3125000000000000000)
  directionHi := (529757307610880712289/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree114.table
  base := (61627271462914474027640034714109584558327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-158308524260836901399462914784300000000000000)
      constant := (4049406872774216423857730178315816021260349663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree114.table
  base := (61627188245475041063548738131772481106587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-706258714873500126578301772940307400000000000000)
      constant := (18235835195638818492362558114267945454673065970054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16554915862840022259/3125000000000000000)
  centralHi := (529757307610880712289/100000000000000000000)
  directionLo := (106419240668754275667/20000000000000000000)
  directionHi := (16628006354492855573/3125000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree115.table
  base := (63319452942676159154607519729025650689407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-159757797991272211033941805691300000000000000)
      constant := (4124792759467116318247465965951036115793798183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree115.table
  base := (31659688377952958802669506243463621903431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-712721708448678435913565255207988400000000000000)
      constant := (18575111856431846272694820054140825056936902636604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106419240668754275667/20000000000000000000)
  centralHi := (16628006354492855573/3125000000000000000)
  directionLo := (534424863061761851663/100000000000000000000)
  directionHi := (33401553941360115729/6250000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree116.table
  base := (32515172320133036484653133007733985355569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-161207071721707520668420696598300000000000000)
      constant := (4200870142973017659434655610953975651903547922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree116.table
  base := (65030274894933336464756485410793457436749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-719184702023856745248828737475669400000000000000)
      constant := (18917499034871221677473904898803088642594157645258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534424863061761851663/100000000000000000000)
  centralHi := (33401553941360115729/6250000000000000000)
  directionLo := (536743419991628509503/100000000000000000000)
  directionHi := (8386615937369195461/1562500000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree117.table
  base := (16689986477329443984325337650306187729243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-162656345452142830302899587505300000000000000)
      constant := (4277639022407044791696657703775676684005334668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree117.table
  base := (66759882065108305993783633482996930881011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-725647695599035054584092219743350400000000000000)
      constant := (19262996727343428622556623846367645373225627732662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536743419991628509503/100000000000000000000)
  centralHi := (8386615937369195461/1562500000000000000)
  directionLo := (269526002247480995713/50000000000000000000)
  directionHi := (539052004494961991427/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree118.table
  base := (68508256161918796091601219716831352964119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-164105619182578139937378478412300000000000000)
      constant := (4355099396964345540910660807305742122207878911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree118.table
  base := (17127049430855046512263428799872483753601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-732110689174213363919355702011031400000000000000)
      constant := (19611604930564207347780980149466570603531388877768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269526002247480995713/50000000000000000000)
  centralHi := (539052004494961991427/100000000000000000000)
  directionLo := (541350744153698684927/100000000000000000000)
  directionHi := (132165709021899093/24414062500000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree119.table
  base := (70275274863233791202974234377204397799111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-165554892913013449571857369319300000000000000)
      constant := (4433251265912730323564846807773592820586982959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree119.table
  base := (70275221376245056587210586287868738032521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-738573682749391673254619184278712400000000000000)
      constant := (19963323641548000927736105355353452641855290878082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541350744153698684927/100000000000000000000)
  centralHi := (132165709021899093/24414062500000000)
  directionLo := (543639763852397149857/100000000000000000000)
  directionHi := (271819881926198574929/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree120.table
  base := (72061001526624798725398390662197059823871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-167004166643448759206336260226300000000000000)
      constant := (4512094628585991768933711581812547774898879399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree120.table
  base := (72060952574765268461496611501442465889597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-745036676324569982589882666546393400000000000000)
      constant := (20318152857580251606511315770708575382777027938474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543639763852397149857/100000000000000000000)
  centralHi := (271819881926198574929/50000000000000000000)
  directionLo := (5459191858574096191/1000000000000000000)
  directionHi := (545919185857409619101/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree121.table
  base := (1477308714184448643969567158695006691449/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-168453440373884068840815151133300000000000000)
      constant := (4591629484377841686952973921780473208029684050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree121.table
  base := (369326954554080284250312892537370906859/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-751499669899748291925146148814074400000000000000)
      constant := (20676092576192280110590980471834161307688538375600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5459191858574096191/1000000000000000000)
  centralHi := (545919185857409619101/100000000000000000000)
  directionLo := (54818912989309059681/10000000000000000000)
  directionHi := (548189129893090596811/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree122.table
  base := (37844288503953093924661178799077366168679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-169902714104319378475294042040300000000000000)
      constant := (4671855832736408107957544982778473828569843102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree122.table
  base := (15137707202623849815527275505276613801177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-757962663474926601260409631081755400000000000000)
      constant := (21037142795138506202317266322932738986050291904170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54818912989309059681/10000000000000000000)
  centralHi := (548189129893090596811/100000000000000000000)
  directionLo := (550449713215176961503/100000000000000000000)
  directionHi := (17201553537974280047/3125000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree123.table
  base := (38765212527827962801223071275152808132841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-171351987834754688109772932947300000000000000)
      constant := (4752773673159240460184086830523768388667718658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree123.table
  base := (1211412305372935259764242961162452251691/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-764425657050104910595673113349436400000000000000)
      constant := (21401303512375791465834186187544485652027012942208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550449713215176961503/100000000000000000000)
  centralHi := (17201553537974280047/3125000000000000000)
  directionLo := (552701050681466834447/100000000000000000000)
  directionHi := (34543815667591677153/6250000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree124.table
  base := (15878195903648024599343807944525830371933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-172801261565189997744251823854300000000000000)
      constant := (4834383005188775789383311573585479308895881385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree124.table
  base := (79390945195628743481728885580660058293653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-770888650625283219930936595617117400000000000000)
      constant := (21768574726044705895733382711768954152294120408026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552701050681466834447/100000000000000000000)
  centralHi := (34543815667591677153/6250000000000000000)
  directionLo := (554943254819917761861/100000000000000000000)
  directionHi := (277471627409958880931/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree125.table
  base := (81270240091209703340870800902969016056437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-174250535295625307378730714761300000000000000)
      constant := (4916683828408223309564870242161164582981262253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree125.table
  base := (81270208688533643668540792885546995564729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-777351644200461529266200077884798400000000000000)
      constant := (22138956434452538491250185003594622781548407656418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554943254819917761861/100000000000000000000)
  centralHi := (277471627409958880931/50000000000000000000)
  directionLo := (278588217947139226339/50000000000000000000)
  directionHi := (557176435894278452679/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree126.table
  base := (20792051624292285548431277749036381170897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-175699809026060617013209605668300000000000000)
      constant := (4999676142437828547768792460885523223291831972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree126.table
  base := (83168177767731590414530380876653411045219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-783814637775639838601463560152479400000000000000)
      constant := (22512448636057888931420733971273036380126957454998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278588217947139226339/50000000000000000000)
  centralHi := (557176435894278452679/100000000000000000000)
  directionLo := (139850175491840596137/25000000000000000000)
  directionHi := (559400701967362384549/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree127.table
  base := (5317804905206199206350121038891965584039/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-177149082756495926647688496575300000000000000)
      constant := (5083359946931481947659790264061489614152790256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree127.table
  base := (21271213050269586466019717862903199695319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-790277631350818147936727042420160400000000000000)
      constant := (22889051329456692686788686185096781547326462316792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139850175491840596137/25000000000000000000)
  centralHi := (559400701967362384549/100000000000000000000)
  directionLo := (561616158962066013931/100000000000000000000)
  directionHi := (140404039740516503483/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree128.table
  base := (10877531977388489014534784206784968383267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-178598356486931236282167387482300000000000000)
      constant := (5167735241573640061793346359039108973733540184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree128.table
  base := (21755057944260177084168177948736882317111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-796740624925996457271990524687841400000000000000)
      constant := (23268764513369545762555488993358068234317632275448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell028.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561616158962066013931/100000000000000000000)
  centralHi := (140404039740516503483/25000000000000000000)
  directionLo := (563822910720229078017/100000000000000000000)
  directionHi := (281911455360114539009/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree129.table
  base := (88974338294388985153821806788360726448811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (67340)
      previous := (57239)
      next := (0)
      square := (1577150824297248719874087163500000000000000)
      linear := (-180047630217366545916646278389300000000000000)
      constant := (5252802026076530422367957406167465834508422259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree129.table
  base := (17794863260559129345647772907408953422587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (295134385)
      previous := (255255637)
      next := (0)
      square := (6967852341745244844403717088343000000000000000)
      linear := (-803203618501174766607254006955522400000000000000)
      constant := (23651588186630207803430181480370434566332672210270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell028.Kernel129
