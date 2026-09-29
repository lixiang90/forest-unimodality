import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell042.Parameters
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch000_049
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch050_099
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch100_149
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch150_199
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch000_049
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch050_099
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch100_149
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree000.table
  base := (419689495128998878109527483/5000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (162568078999670677375899430000000000000)
      linear := (7290643583592863350914537000000000000)
      constant := (209844747564499439054763741500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree000.table
  base := (419689495128998878109527483/5000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (162568078999670677375899430000000000000)
      linear := (7290643583592863350914537000000000000)
      constant := (209844747564499439054763741500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree001.table
  base := (120469583297928632641332697520621710490429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-1401378466604278191524803745427312500000000)
      constant := (1133818515848934700118367633330554112969290211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree001.table
  base := (480882282079454480960396802514832202786459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-50597460144594340417131643379539500000000000)
      constant := (40733187786801255608315809076348102412597634579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49961995729029094919/100000000000000000000)
  directionHi := (1249049893225727373/2500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree002.table
  base := (144201292969424974798662770331326558316027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-5742709197373163268636724738975250000000000)
      constant := (1359483465527335413811879919431865036414248043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree002.table
  base := (8979003138071582655973287725094963279937/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-25916109061599397469984615597466750000000000)
      constant := (6094997945740540615904487145161481145004260776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49961995729029094919/100000000000000000000)
  centralHi := (1249049893225727373/2500000000000000000)
  directionLo := (35328465981609798181/50000000000000000000)
  directionHi := (70656931963219596363/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree003.table
  base := (18182478051607133786655948643188496677929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-8682661461537770154223841987095875000000000)
      constant := (861553940279559913210605149917896540080357305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree003.table
  base := (180941278465678218791996041562695756062613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-17414601372022315482527253488910500000000000)
      constant := (1714865040220206910285335370695336767230625717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35328465981609798181/50000000000000000000)
  centralHi := (70656931963219596363/100000000000000000000)
  directionLo := (86536715050217642091/100000000000000000000)
  directionHi := (21634178762554410523/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree004.table
  base := (7597686059185048538555592876232062074559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-5811306862851188519905479617608250000000000)
      constant := (291465359667742399822317774770914724175602524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree004.table
  base := (60450883305669530986373559293704825850371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-104899194225002044402776050205261000000000000)
      constant := (5218942951406195794391653472648013295335266651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86536715050217642091/100000000000000000000)
  centralHi := (21634178762554410523/25000000000000000000)
  directionLo := (99923991458058189839/100000000000000000000)
  directionHi := (1249049893225727373/1250000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree005.table
  base := (43116503087489556101088214495063124562031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-14562565989866983925398076483337125000000000)
      constant := (423011979368621624785709673257450262246337179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree005.table
  base := (85753518309383972136483359596498608134533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-262865364551807338268358919420849500000000000)
      constant := (7575373927901307104090648630001087346377888973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99923991458058189839/100000000000000000000)
  centralHi := (1249049893225727373/1250000000000000000)
  directionLo := (13964802342707902391/12500000000000000000)
  directionHi := (111718418741663219129/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree006.table
  base := (64502745591625032138828549550418722101941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-35005036508063181621970387462915500000000000)
      constant := (656971499134551928109540117785947092194662869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree006.table
  base := (6415423983958136275508167524152536657277/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-17551796702978365985064763246176500000000000)
      constant := (326987370151426542205669558958788758916596465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13964802342707902391/12500000000000000000)
  centralHi := (111718418741663219129/100000000000000000000)
  directionLo := (61190698033616860211/50000000000000000000)
  directionHi := (122381396067233720423/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree007.table
  base := (50353975886099302332658660337375522525849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-40884941036392395393144621959156750000000000)
      constant := (542078634367585641311426166996309703555088241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree007.table
  base := (25047315460166428278728093255282854356521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-184499658377706918596986278720752250000000000)
      constant := (2430104275069735684962346959229301401483304801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61190698033616860211/50000000000000000000)
  centralHi := (122381396067233720423/100000000000000000000)
  directionLo := (132187015703482203447/100000000000000000000)
  directionHi := (16523376962935275431/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree008.table
  base := (20280662575726788853018511891209946902839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-23382422782360804582159428227699000000000000)
      constant := (235498920081933705170829646681624827908812151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree008.table
  base := (40361347801321782405323361866398650876711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-422066292857217086656779376451832000000000000)
      constant := (4226572428022121906097586467498892654890764191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132187015703482203447/100000000000000000000)
  centralHi := (16523376962935275431/12500000000000000000)
  directionLo := (5652554557057567709/4000000000000000000)
  directionHi := (70656931963219596363/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree009.table
  base := (33374708523094074201839304543808364168291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-52644750093050822935493090951639250000000000)
      constant := (427262568032434321006756625656302623068825019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree009.table
  base := (8303595818611763921943458043797379955543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-13198146359972787114432949873948875000000000)
      constant := (106597742944011706174564261687689256986079087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5652554557057567709/4000000000000000000)
  centralHi := (70656931963219596363/50000000000000000000)
  directionLo := (149885987187087284759/100000000000000000000)
  directionHi := (3747149679677182119/2500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree010.table
  base := (1739197466242140205324927080265836120931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-14631163655345009176666831361970125000000000)
      constant := (100443657446909624535539418020232498481734116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree010.table
  base := (13846987283908468978888113918261619771197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-264100122530411792791196507236243500000000000)
      constant := (1805886916369902807525905684549807770719733157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149885987187087284759/100000000000000000000)
  centralHi := (3747149679677182119/2500000000000000000)
  directionLo := (7899685147566834391/5000000000000000000)
  directionHi := (157993702951336687821/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree011.table
  base := (467405674549116379764145096239187882121/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-32202279574854625238920779972060875000000000)
      constant := (194687092039295598627906359318763761564099725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree011.table
  base := (4651294509435997796631564603473429480681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-581267221162626835045199833482814500000000000)
      constant := (3503300935950728274099461716260260620205238805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7899685147566834391/5000000000000000000)
  centralHi := (157993702951336687821/100000000000000000000)
  directionLo := (33141038722105700917/20000000000000000000)
  directionHi := (82852596805264252293/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree012.table
  base := (2460225465710287450521160698628683857551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-17571115919509616062253948610090750000000000)
      constant := (96757230241354973447356460629505721268894718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree012.table
  base := (19582570126696294533820504431747202395219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-70481577473825564945334072499238000000000000)
      constant := (387228979142353291389814014563242302336615571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33141038722105700917/20000000000000000000)
  centralHi := (82852596805264252293/50000000000000000000)
  directionLo := (173073430100435284183/100000000000000000000)
  directionHi := (21634178762554410523/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree013.table
  base := (4140889988070337970733928235862941687727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-19041092051591919505047507234151062500000000)
      constant := (98218589422811051048085775422864165898417093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree013.table
  base := (16475903230399807982837010182007945049899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-687401173366233333970813471503469500000000000)
      constant := (3540425155414278865863577148771013880707997219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173073430100435284183/100000000000000000000)
  centralHi := (21634178762554410523/12500000000000000000)
  directionLo := (9007026871276361939/5000000000000000000)
  directionHi := (180140537425527238781/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree014.table
  base := (3471780982055975651909139351900892184793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-20511068183674222947841065858211375000000000)
      constant := (101425527674219894641758714836741687926092337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree014.table
  base := (6904550799725230675806686192410212848389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-370234074734018291716810145256898500000000000)
      constant := (1829304062230595103834949487518790656089428909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9007026871276361939/5000000000000000000)
  centralHi := (180140537425527238781/100000000000000000000)
  directionLo := (23367583797186227977/12500000000000000000)
  directionHi := (186940670377489823817/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree015.table
  base := (2891131436434032067239041765119756530397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-21981044315756526390634624482271687500000000)
      constant := (106171117780020527878587536639952275034349123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree015.table
  base := (11494808700921923416318862578224152647481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-88170569507759981432936345502680500000000000)
      constant := (425801364539686554840231299220178513197648729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23367583797186227977/12500000000000000000)
  centralHi := (186940670377489823817/100000000000000000000)
  directionLo := (24187747175226971863/12500000000000000000)
  directionHi := (38700395480363154981/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree016.table
  base := (953227499324758985288530698039368485433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-46902040895677659666856366212664000000000000)
      constant := (224612028839192771175738035975927340397195485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree016.table
  base := (9469887352518538701875677213755822758351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-846602101671643082359233928534452000000000000)
      constant := (4055891104868266822255061820315668826999921031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24187747175226971863/12500000000000000000)
  centralHi := (38700395480363154981/20000000000000000000)
  directionLo := (99923991458058189839/50000000000000000000)
  directionHi := (199847982916116379679/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree017.table
  base := (7742455797006491357908501276586463055799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-99683986319684533104886966921569250000000000)
      constant := (478870029915659222500153522866932474251387791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree017.table
  base := (384331347378387577274281591177172114691/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-224917269443361582955510186886194875000000000)
      constant := (1081401103652703751916856574528974908830117855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99923991458058189839/50000000000000000000)
  centralHi := (199847982916116379679/100000000000000000000)
  directionLo := (51499646414361347701/25000000000000000000)
  directionHi := (41199717131489078161/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree018.table
  base := (246304703742315135868746523809005033649/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-105563890848013746876061201417810500000000000)
      constant := (513270015480355486130210119097334982477586025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree018.table
  base := (6107700246731301125207781731897699713891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-105859561541694397920538618506123000000000000)
      constant := (515354589125602253904043776700028050358000419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51499646414361347701/25000000000000000000)
  centralHi := (41199717131489078161/20000000000000000000)
  directionLo := (6624087371551837159/3125000000000000000)
  directionHi := (211970795889658789089/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree019.table
  base := (2373864097778348115223261916121517938087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-55721897688171480323617717957025875000000000)
      constant := (276070720760872356601812456173699607396648083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree019.table
  base := (188126168123834119603719849225610702481/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-1005803029977052830747654385565434500000000000)
      constant := (4991115313461414580021141559369478333357339025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624087371551837159/3125000000000000000)
  centralHi := (211970795889658789089/100000000000000000000)
  directionLo := (217779290400448565969/100000000000000000000)
  directionHi := (21777929040044856597/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree020.table
  base := (3488268231445671137617154966380198331351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-117323699904672174418409670410293000000000000)
      constant := (595253605272844515275040300160589879849681559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree020.table
  base := (1724262690461771542968094424690413211279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-529435003039428040105230602287881000000000000)
      constant := (2691152430201039913173764038962227318644316999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217779290400448565969/100000000000000000000)
  centralHi := (21777929040044856597/10000000000000000000)
  directionLo := (223436837483326438257/100000000000000000000)
  directionHi := (111718418741663219129/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree021.table
  base := (2358974104672612347763461297441043705677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-123203604433001388189583904906534250000000000)
      constant := (642415846553695329385131383798266864211089893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree021.table
  base := (464718838276887898166114423127556658393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-123548553575628814408140891509565500000000000)
      constant := (645560858661189839892951652889774176431598685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223436837483326438257/100000000000000000000)
  centralHi := (111718418741663219129/50000000000000000000)
  directionLo := (57238656824834053731/25000000000000000000)
  directionHi := (9158185091973448597/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree022.table
  base := (335740688845687039535933150374393057121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-32270877240332650490189534850693875000000000)
      constant := (173367328163530902145700352940872904508826489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree022.table
  base := (655757732405248274417730870015808335841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-582501979141231289568037421298208500000000000)
      constant := (3136458725147320501948769433655534962562351721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57238656824834053731/25000000000000000000)
  centralHi := (9158185091973448597/4000000000000000000)
  directionLo := (234342532159668944469/100000000000000000000)
  directionHi := (23434253215966894447/10000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree023.table
  base := (213045739466031692606078917703303287187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-67481706744829907865966186949508375000000000)
      constant := (374140467433066907003033923975664992933829983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree023.table
  base := (24886318007880397039410445518201506241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-304517733596066457149720415401686125000000000)
      constant := (1692429834577629978527665131005072605359351484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234342532159668944469/100000000000000000000)
  centralHi := (23434253215966894447/10000000000000000000)
  directionLo := (239609314084893192001/100000000000000000000)
  directionHi := (119804657042446596001/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree024.table
  base := (-403529878712082261722383431390749451781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-140843318017989029503106608395258000000000000)
      constant := (806738838730432833159817940230653313408192571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree024.table
  base := (-107066640004275257981330642505337981309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-35309386402390807723935791128252000000000000)
      constant := (202762479910137473781747721391935899933863619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239609314084893192001/100000000000000000000)
  centralHi := (119804657042446596001/50000000000000000000)
  directionLo := (48952558426893488169/20000000000000000000)
  directionHi := (122381396067233720423/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree025.table
  base := (-28898061862796029174420631519585061791/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-36680805636579560818570210722874812500000000)
      constant := (217187183795290943565003414003287219563428560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree025.table
  base := (-235563542968820732700888348640054764517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-1324204886587872327524495299627399500000000000)
      constant := (7861261282548836982147887725344137885867179615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48952558426893488169/20000000000000000000)
  centralHi := (122381396067233720423/50000000000000000000)
  directionLo := (124904989322572737299/50000000000000000000)
  directionHi := (249809978645145474599/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree026.table
  base := (-367909396145325995328706445422504593911/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-152603127074647457045455077387740500000000000)
      constant := (934231017753037786083571937018840607316957005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree026.table
  base := (-371780730961699500853173051756578736659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-1377271862689675576987302118637727000000000000)
      constant := (8454441386571456426073977170865696373754896105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124904989322572737299/50000000000000000000)
  centralHi := (249809978645145474599/100000000000000000000)
  directionLo := (127378595580179364343/50000000000000000000)
  directionHi := (254757191160358728687/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree027.table
  base := (-1230777842772852680619472544529337852833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-79241515801488335408314655941990875000000000)
      constant := (501559195283241076308801796074651533384881803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree027.table
  base := (-2478648861077036451476907871871116929101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-158926537643497647383345437516450500000000000)
      constant := (1008709586738125055682965869544175934251588691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127378595580179364343/50000000000000000000)
  centralHi := (254757191160358728687/100000000000000000000)
  directionLo := (10384405806026117051/4000000000000000000)
  directionHi := (64902536287663231569/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree028.table
  base := (-757000178493202889989007420673019258433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-41090734032826471146950886595055750000000000)
      constant := (268838477294334161078885501463237897734903903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree028.table
  base := (-38038491610666392850366706297383306321/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-370851453723320518978228939164595500000000000)
      constant := (2433146419366002231106159243943753903498627980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10384405806026117051/4000000000000000000)
  centralHi := (64902536287663231569/25000000000000000000)
  directionLo := (52874806281392881379/20000000000000000000)
  directionHi := (16523376962935275431/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree029.table
  base := (-708801449421164146943396049032430879829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-170242840659635098358977780876464250000000000)
      constant := (1150889350756651382005861252552447216992819695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree029.table
  base := (-1778647929587054200955741902006554350023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-768236395497542662687861287834354750000000000)
      constant := (5208303818050755311676294811704045389054452337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52874806281392881379/20000000000000000000)
  centralHi := (16523376962935275431/6250000000000000000)
  directionLo := (10762143243766875203/4000000000000000000)
  directionHi := (67263395273542970019/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree030.table
  base := (-4013918322377696223731865079420675565277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-176122745187964312130152015372705500000000000)
      constant := (1229683851665219613639342799585316762043808707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree030.table
  base := (-4025618895826620474254303789855254081823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-176615529677432063870947710519893000000000000)
      constant := (1236676255228365255437075605739600508094127393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10762143243766875203/4000000000000000000)
  centralHi := (67263395273542970019/25000000000000000000)
  directionLo := (273653120787660021997/100000000000000000000)
  directionHi := (136826560393830010999/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree031.table
  base := (-444141627771214078235246205764710832149/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-91001324858146762950663124934473375000000000)
      constant := (655851382392758609995440884476111806831237795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree031.table
  base := (-34778984124663551124475537657511832173/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-410651685799672956075334053422341125000000000)
      constant := (2968177899593929791621067364525163296881636984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273653120787660021997/100000000000000000000)
  centralHi := (136826560393830010999/50000000000000000000)
  directionLo := (139088309657976977641/50000000000000000000)
  directionHi := (278176619315953955283/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree032.table
  base := (-1207406210664255973855008644722204089219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-46970638561155684918125121091297000000000000)
      constant := (349229174736557074269401678332882781724538429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree032.table
  base := (-4838673745966023448730094835703662099097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-1695673719300495073764143032699692000000000000)
      constant := (12644220633468581445128061537960342189786366943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139088309657976977641/50000000000000000000)
  centralHi := (278176619315953955283/100000000000000000000)
  directionLo := (282627727852878385451/100000000000000000000)
  directionHi := (70656931963219596363/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree033.table
  base := (-2590597552278308739139420734642699767143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-96881229386475976721837359430714625000000000)
      constant := (742650355033265295224021750714045903320639013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree033.table
  base := (-5189143945732730667779670831749763668931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-194304521711366480358549983523335500000000000)
      constant := (1493821152959948643356504085936352934576528221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282627727852878385451/100000000000000000000)
  centralHi := (70656931963219596363/25000000000000000000)
  directionLo := (17938113400717066383/6250000000000000000)
  directionHi := (287009814411473062129/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree034.table
  base := (-1374594497146401331027325704132647520337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-49910590825320291803712238339417625000000000)
      constant := (394208404797863875073039390159198831590524167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree034.table
  base := (-5505355727212605199054633927577321628719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-1801807671504101572689756670720347000000000000)
      constant := (14273031552308392357028340408203617670908446361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17938113400717066383/6250000000000000000)
  centralHi := (287009814411473062129/100000000000000000000)
  directionLo := (145662996833217505159/50000000000000000000)
  directionHi := (291325993666435010319/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree035.table
  base := (-722885678607191681332901866097347324609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-51380566957402595246505796963477937500000000)
      constant := (417874359233232168032230559873554256229101588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree035.table
  base := (-5789206771117766681832614843253112462329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-1854874647605904822152563489730674500000000000)
      constant := (15129983462974762142413803395283691269515017951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145662996833217505159/50000000000000000000)
  centralHi := (291325993666435010319/100000000000000000000)
  directionLo := (147789576427909195483/50000000000000000000)
  directionHi := (295579152855818390967/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree036.table
  base := (-241477681530263698333589227309062054287/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-211402172357939594757197422350153000000000000)
      constant := (1769276877308322756599181908583518722030340425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree036.table
  base := (-1510577211684000556445033895257643198351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-52998378436325224211538064131694500000000000)
      constant := (444864156177877445725868194027627053896715441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147789576427909195483/50000000000000000000)
  centralHi := (295579152855818390967/100000000000000000000)
  directionLo := (149885987187087284759/50000000000000000000)
  directionHi := (299771974374174569519/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree037.table
  base := (-195666524507701341097951309742308452519/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-54320519221567202132092914211598562500000000)
      constant := (467539736698693042854666511086107088533083582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree037.table
  base := (-78325392280375604137357918974125903857/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-490252149952377830269544281937832375000000000)
      constant := (4232073516507921294654113042203200939444082660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149885987187087284759/50000000000000000000)
  centralHi := (299771974374174569519/100000000000000000000)
  directionLo := (60781391111891572537/20000000000000000000)
  directionHi := (151953477779728931343/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree038.table
  base := (-258296797247581265124936874570372211673/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-223161981414598022299545891342635500000000000)
      constant := (1974132596738890654579595873582763782446718575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree038.table
  base := (-1615384575654173232718537962216385662711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-503518893977828642635245986690414250000000000)
      constant := (4467359557893878880219947748237468519133469809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60781391111891572537/20000000000000000000)
  centralHi := (151953477779728931343/50000000000000000000)
  directionLo := (307986426088303147857/100000000000000000000)
  directionHi := (153993213044151573929/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree039.table
  base := (-6626214305640336347719180922467928794947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-229041885942927236070720125838876750000000000)
      constant := (2081188429181627124928340086112169295077718677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree039.table
  base := (-265192767603457009041144393238606627821/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-229682505779235313333754529530220500000000000)
      constant := (2093162035574977517436216349199212591908305275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307986426088303147857/100000000000000000000)
  centralHi := (153993213044151573929/50000000000000000000)
  directionLo := (78003140830944004429/25000000000000000000)
  directionHi := (312012563323776017717/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree040.table
  base := (-169214044286703107151843968815762960763/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-58730447617814112460473590083779500000000000)
      constant := (547829611938458911816440035178222831771809330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree040.table
  base := (-3385857831103512432350716049739877761799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-1060104764057460534733298792391156000000000000)
      constant := (9917641531414605319180755545402123661253098881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78003140830944004429/25000000000000000000)
  centralHi := (312012563323776017717/100000000000000000000)
  directionLo := (315987405902673375641/100000000000000000000)
  directionHi := (157993702951336687821/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree041.table
  base := (-430324103764132681441919900883227233571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-60200423749896415903267148707839812500000000)
      constant := (576128961657232976105452898139795134739665594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree041.table
  base := (-17219859268882577916487681601526369187/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-543319126054181079732351100948159875000000000)
      constant := (5214962957227568475263689832744592308946940300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315987405902673375641/100000000000000000000)
  centralHi := (157993702951336687821/50000000000000000000)
  directionLo := (19994554112691416649/6250000000000000000)
  directionHi := (63982573160612533277/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree042.table
  base := (-3488350891976252930065169697161787477957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-123340799763957438692121414663800250000000000)
      constant := (1210387415815724360208095515977269597088652587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree042.table
  base := (-1744778152708820234716630495211237087329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-61842874453292432455339200633415750000000000)
      constant := (608669806210538585370523076348383306182821439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19994554112691416649/6250000000000000000)
  centralHi := (63982573160612533277/20000000000000000000)
  directionLo := (323790739094798546589/100000000000000000000)
  directionHi := (32379073909479854659/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree043.table
  base := (-3521817279289758189134801919958211994109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-126280752028122045577708531911920875000000000)
      constant := (1270045234265939809391174836940286037839615919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree043.table
  base := (-7045740994664314222282747751995517294857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-2279410456420330817855018041813294500000000000)
      constant := (22992022729355273014021537757465017310891714383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323790739094798546589/100000000000000000000)
  centralHi := (32379073909479854659/10000000000000000000)
  directionLo := (65524543108909481489/20000000000000000000)
  directionHi := (163811357772273703723/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree044.table
  base := (-3543215341549702814779314930142608073163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-129220704292286652463295649160041500000000000)
      constant := (1331229277169703254121139888523084747514609333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree044.table
  base := (-443016901462960776549484496016119601487/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-583119358130533516829456215205905500000000000)
      constant := (6024885888531435838359108900473428372855917412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65524543108909481489/20000000000000000000)
  centralHi := (163811357772273703723/50000000000000000000)
  directionLo := (33141038722105700917/10000000000000000000)
  directionHi := (331410387221057009171/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree045.table
  base := (-355273537496528939758934342115074835941/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-66080328278225629674441383204081062500000000)
      constant := (696968877014991153611561694447564270651749405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree045.table
  base := (-7107076944514398294264386567762610301747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-265060489847104146308959075537105500000000000)
      constant := (2803849294868521276639008073413964998108362477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33141038722105700917/10000000000000000000)
  centralHi := (331410387221057009171/100000000000000000000)
  directionLo := (67031051244997931477/20000000000000000000)
  directionHi := (167577628112494828693/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree046.table
  base := (-1420215820669943368402968524267568477961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-270201217641231732468939767312565500000000000)
      constant := (2916338277938254646176829072849814264391824755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree046.table
  base := (-284099235359381765414493818498125452489/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-2438611384725740566243438498844277000000000000)
      constant := (26397295902902183206654392039933017807694474775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67031051244997931477/20000000000000000000)
  centralHi := (167577628112494828693/50000000000000000000)
  directionLo := (169429370824885310091/50000000000000000000)
  directionHi := (338858741649770620183/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree047.table
  base := (-7073532213586755586743327904982456646179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-276081122169560946240114001808806750000000000)
      constant := (3047844262665883137334920007497143633775476789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree047.table
  base := (-3537377581645148967166619457084342994781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-1245839180413771907853122658927302250000000000)
      constant := (13793738595059503374491479926111557575077700139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169429370824885310091/50000000000000000000)
  centralHi := (338858741649770620183/100000000000000000000)
  directionLo := (342522185864935632977/100000000000000000000)
  directionHi := (171261092932467816489/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree048.table
  base := (-7023065792707536570690600435016014071431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-281961026697890160011288236305048000000000000)
      constant := (3182391244428022584858178940839830823601905721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree048.table
  base := (-878016545443735704365391217378698871377/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-70687370470259640699140337135137000000000000)
      constant := (800143550562930267377622659785113644638427614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342522185864935632977/100000000000000000000)
  centralHi := (171261092932467816489/50000000000000000000)
  directionLo := (173073430100435284183/50000000000000000000)
  directionHi := (346146860200870568367/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree049.table
  base := (-868735105434280668208749666296463210343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-71960232806554843445615617700322312500000000)
      constant := (829994332997420896222398545981458359897609176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree049.table
  base := (-6950810727772984887903478236195296003679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-2597812313031150314631858955875259500000000000)
      constant := (30050351005925329323343781710462825037549958601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173073430100435284183/50000000000000000000)
  centralHi := (346146860200870568367/100000000000000000000)
  directionLo := (349733970103203664437/100000000000000000000)
  directionHi := (174866985051601832219/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree050.table
  base := (-6854148802925534024196290481412279405703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-293720835754548587553636705297530500000000000)
      constant := (3460600912299769459702514248038728386509240473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree050.table
  base := (-685495926254306706359938040603570427979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-1325439644566476782047332887442793500000000000)
      constant := (15661506217726015451560279136205996434816551505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349733970103203664437/100000000000000000000)
  centralHi := (174866985051601832219/50000000000000000000)
  directionLo := (353284659816097981813/100000000000000000000)
  directionHi := (176642329908048990907/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree051.table
  base := (-6736015917578446751520629250315955997937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-299600740282877801324810939793771750000000000)
      constant := (3604260609324801340934271068829780785249785767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree051.table
  base := (-1684180518914779031860670240791785771393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-75109618478743244821040905385997625000000000)
      constant := (906198330712585238993000316550921374786338263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353284659816097981813/100000000000000000000)
  centralHi := (176642329908048990907/50000000000000000000)
  directionLo := (17840000832301241629/5000000000000000000)
  directionHi := (356800016646024832581/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree052.table
  base := (-6595606966188475486435220438898920272653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-305480644811207015095985174290013000000000000)
      constant := (3750955249021468804744588772500702152904607923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree052.table
  base := (-6596222065301947534587390506224017950811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-2757013241336560063020279412906242000000000000)
      constant := (33950723009387592791668244309223394810907373709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17840000832301241629/5000000000000000000)
  centralHi := (356800016646024832581/100000000000000000000)
  directionLo := (360281074851054477561/100000000000000000000)
  directionHi := (180140537425527238781/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree053.table
  base := (-6433028428297307129209195010418388367591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-311360549339536228867159408786254250000000000)
      constant := (3900683829523764119088835105818205342833711281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree053.table
  base := (-6433564058598095538045308168607977134641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-2810080217438363312483086231916569500000000000)
      constant := (35305752869789701419801964850167083849198965479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360281074851054477561/100000000000000000000)
  centralHi := (180140537425527238781/50000000000000000000)
  directionLo := (72745763839019146191/20000000000000000000)
  directionHi := (90932204798773932739/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree054.table
  base := (-1562092795458675703934425975573642432827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-79310113466966360659583410820623875000000000)
      constant := (1013361373940311540359843148403025901083905757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree054.table
  base := (-6248837482509731687504227048681661439369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-318127465948907395771765894547433000000000000)
      constant := (4076469101566090093238895667922421091266977079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72745763839019146191/20000000000000000000)
  centralHi := (90932204798773932739/25000000000000000000)
  directionLo := (367144188201701161267/100000000000000000000)
  directionHi := (91786047050425290317/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree055.table
  base := (-755214100048648641708994838996130828903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-80780089599048664102376969444684187500000000)
      constant := (1052309879461005121283247746490517272464047096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree055.table
  base := (-6042118637348415915570697726700676051057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-2916214169641969811408699869937224500000000000)
      constant := (38098123681116237843059477482940887824757942183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367144188201701161267/100000000000000000000)
  centralHi := (91786047050425290317/25000000000000000000)
  directionLo := (370528077137905547557/100000000000000000000)
  directionHi := (185264038568952773779/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree056.table
  base := (-5813119510058956882043671507136020717541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-329000262924523870180682112274978000000000000)
      constant := (4368065272650729212941600904023167056068656731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree056.table
  base := (-5813472632529574983800830689399698625009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-2969281145743773060871506688947552000000000000)
      constant := (39535452657323574677934881272957198620735612871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370528077137905547557/100000000000000000000)
  centralHi := (185264038568952773779/50000000000000000000)
  directionLo := (23367583797186227977/6250000000000000000)
  directionHi := (373881340754979647633/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree057.table
  base := (-5562647856734701388696286541545389211431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-334880167452853083951856346771219250000000000)
      constant := (4529922228141086792525523380811864720019020721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree057.table
  base := (-2781477517573854655338731562846294932497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-167908228991420906129684083775437750000000000)
      constant := (2277789118735538441879929291408683753948885727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23367583797186227977/6250000000000000000)
  centralHi := (373881340754979647633/100000000000000000000)
  directionLo := (188602397904936992579/50000000000000000000)
  directionHi := (377204795809873985159/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree058.table
  base := (-2645173063496902027486538586992937839517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-170380035990591148861515290633730250000000000)
      constant := (2347404964993343321139759778647659490836734547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree058.table
  base := (-5290613274302513262020709926770878199987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-3075415097947379559797120326968207000000000000)
      constant := (42492374104520998452179002251037224856896900853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188602397904936992579/50000000000000000000)
  centralHi := (377204795809873985159/100000000000000000000)
  directionLo := (38049922338842723093/10000000000000000000)
  directionHi := (380499223388427230931/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree059.table
  base := (-199850222371384894111450095534139775259/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-346639976509511511494204815763701750000000000)
      constant := (4862727990174968166750367459144052242849076725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree059.table
  base := (-4996487837627281398074548504828429272973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-3128482074049182809259927145978534500000000000)
      constant := (44011959130634219156299686038757961741672873387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38049922338842723093/10000000000000000000)
  centralHi := (380499223388427230931/100000000000000000000)
  directionLo := (383765371049061394849/100000000000000000000)
  directionHi := (7675307420981227897/2000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree060.table
  base := (-4680411376569189676063898742217967720297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-352519881037840725265379050259943000000000000)
      constant := (5033676077293081593734597719937890985469725527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree060.table
  base := (-4680613290981325411309803014471280891111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-353505450016776228746970440554318000000000000)
      constant := (5062106254278646854752295194253591593095536601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383765371049061394849/100000000000000000000)
  centralHi := (7675307420981227897/2000000000000000000)
  directionLo := (387003954803631549809/100000000000000000000)
  directionHi := (38700395480363154981/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree061.table
  base := (-2171421833459694604394543313845415010419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-179199892783084969518276642378092125000000000)
      constant := (2603826954121179287177056815178728891534155129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree061.table
  base := (-434301914761451288477374704253257329881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-1617308013126394654092770391999594750000000000)
      constant := (23566681539465147012395944102501847748210485195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387003954803631549809/100000000000000000000)
  centralHi := (38700395480363154981/10000000000000000000)
  directionLo := (390215660950299139629/100000000000000000000)
  directionHi := (39021566095029913963/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree062.table
  base := (-995894533649181760479584897523948278041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-91069922523624788201931879813106375000000000)
      constant := (1346165310292850649449776315091200457761287231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree062.table
  base := (-995932652291354926635984565053999675243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-821920750588648139412086900752379250000000000)
      constant := (12183794341950419976896271186941718839438247517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390215660950299139629/100000000000000000000)
  centralHi := (39021566095029913963/10000000000000000000)
  directionLo := (393401147771719565887/100000000000000000000)
  directionHi := (6146892933933118217/1562500000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree063.table
  base := (-1801318370390214352124888588062705984903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-185079797311414183289450876874333375000000000)
      constant := (2782348934723739165534555551572546439817735173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree063.table
  base := (-45034614968826931879042222927461092063/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-92798610512677661308643178389440125000000000)
      constant := (1399011037017453536293122292632684174429959660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393401147771719565887/100000000000000000000)
  centralHi := (6146892933933118217/1562500000000000000)
  directionLo := (396561047110446610343/100000000000000000000)
  directionHi := (49570130888805826293/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree064.table
  base := (-400004781281364667290887087045178176099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-94009874787789395087518997061227000000000000)
      constant := (1436940904128191693203984377675766837082169018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree064.table
  base := (-200009580850303778559384280949912672157/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-848454238639549764143490310257543000000000000)
      constant := (13005255354222868225213157970578143780036292332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396561047110446610343/100000000000000000000)
  centralHi := (49570130888805826293/12500000000000000000)
  directionLo := (399695965832232759357/100000000000000000000)
  directionHi := (199847982916116379679/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree065.table
  base := (-1387899348954132725845926739627009406887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-190959701839743397060625111370574625000000000)
      constant := (2966929165747446570408062994476668721420287717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree065.table
  base := (-55517971943274373286931302689017058157/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-1723441965330001153018384030020249750000000000)
      constant := (26852524145562318140538636621535243486673927075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399695965832232759357/100000000000000000000)
  centralHi := (199847982916116379679/50000000000000000000)
  directionLo := (40280648718682386549/10000000000000000000)
  directionHi := (402806487186823865491/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree066.table
  base := (-2329931786942421891725132641669995319613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-387799308207816007892424457237390500000000000)
      constant := (6122981885460543206364667908031303412475261283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree066.table
  base := (-2330018518740500895628079216438604821203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-388883434084645061722174986561203000000000000)
      constant := (6157386313300930531104576341287368260987300973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40280648718682386549/10000000000000000000)
  centralHi := (402806487186823865491/100000000000000000000)
  directionLo := (202946586037445096787/50000000000000000000)
  directionHi := (16235726882995607743/4000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree067.table
  base := (-5820153839745305217202752972638171063/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-98419803184036305415899672933407937500000000)
      constant := (1578783542054370659989582716700072215311052390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree067.table
  base := (-1862524514320000242054860463571971042611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-3553017882863608804962381698061154500000000000)
      constant := (57155306032538440133683370935596646506078157909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202946586037445096787/50000000000000000000)
  centralHi := (16235726882995607743/4000000000000000000)
  directionLo := (408956560228887808913/100000000000000000000)
  directionHi := (204478280114443904457/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree068.table
  base := (-686680516474638076230895651143882834531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-199779558632237217717386463114936500000000000)
      constant := (3255157542792161931446479737908860378284897821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree068.table
  base := (-1373426370821219802694611050577131181829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-3606084858965412054425188517071482000000000000)
      constant := (58921535100848744240871672747243495829391538451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408956560228887808913/100000000000000000000)
  centralHi := (204478280114443904457/50000000000000000000)
  directionLo := (51499646414361347701/12500000000000000000)
  directionHi := (411997171314890781609/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree069.table
  base := (-43133787772935974546242006670303973559/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-101359755448200912301486790181528562500000000)
      constant := (1677131139264829803824027098943190148685010595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree069.table
  base := (-2156831124418540291797690777537716417/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-101643106529644869552444314891161375000000000)
      constant := (1686532314349364894847569164998210643482619700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51499646414361347701/12500000000000000000)
  centralHi := (411997171314890781609/100000000000000000000)
  directionLo := (83003101192352803563/20000000000000000000)
  directionHi := (51876938245220502227/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree070.table
  base := (-165200354880486656730135299926979506287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-205659463160566431488560697611177750000000000)
      constant := (3454881256914807050474298922408807967794095617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree070.table
  base := (-330449895275461239448042597246168757159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-3712218811169018553350802155092137000000000000)
      constant := (62536190074752655212089287685568683277225018721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83003101192352803563/20000000000000000000)
  centralHi := (51876938245220502227/12500000000000000000)
  directionLo := (418012046723448517573/100000000000000000000)
  directionHi := (209006023361724258787/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree071.table
  base := (223457852239244099731165081676704928401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-417198830849462076748295629718596750000000000)
      constant := (7114028897071037025552018945345432778780700009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree071.table
  base := (223415188389886801102518201723829317589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-3765285787270821802813608974102464500000000000)
      constant := (64384614858460057259031645468609896613880254109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418012046723448517573/100000000000000000000)
  centralHi := (209006023361724258787/50000000000000000000)
  directionLo := (210493629489798353409/50000000000000000000)
  directionHi := (420987258979596706819/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree072.table
  base := (199723646475269401488083024590368643297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-105769683844447822629867466053709500000000000)
      constant := (1830330914123965545767183588975586497314781473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree072.table
  base := (199714396306596681254103526457884061839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-106065354538128473674344883142022000000000000)
      constant := (1840567700722307126708749450999874356137843151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210493629489798353409/50000000000000000000)
  centralHi := (420987258979596706819/100000000000000000000)
  directionLo := (6624087371551837159/1562500000000000000)
  directionHi := (423941591779317578177/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree073.table
  base := (1395904921999048335806609862827930057897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-428958639906120504290644098711079250000000000)
      constant := (7531646749112247042816591273381768468524127873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree073.table
  base := (1395872838058833282512681629357239218413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-3871419739474428301739222612123119500000000000)
      constant := (68163656799943599563782590218791192897691931253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624087371551837159/1562500000000000000)
  centralHi := (423941591779317578177/100000000000000000000)
  directionLo := (21343773931618154153/5000000000000000000)
  directionHi := (426875478632363083061/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree074.table
  base := (251810619260156555019984179927551167919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-108709636108612429515454583301830125000000000)
      constant := (1936249534541096410369771679066029023112274742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree074.table
  base := (1007228569004492260830365286229535201211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-1962243357788115775601014715566723500000000000)
      constant := (35047136628871033929551520554142117817248748691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21343773931618154153/5000000000000000000)
  centralHi := (426875478632363083061/100000000000000000000)
  directionLo := (53723667281462848399/12500000000000000000)
  directionHi := (429789338251702787193/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree075.table
  base := (132731567111363128926769719255880912867/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-110179612240694732958248141925890437500000000)
      constant := (1990344448056741669552418786657250376041921765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree075.table
  base := (2654607230100697372074698728230834851647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-441950410186448311184981805571530500000000000)
      constant := (8005809591529314075125887522992397948556646623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53723667281462848399/12500000000000000000)
  centralHi := (429789338251702787193/100000000000000000000)
  directionLo := (216341787625544105229/50000000000000000000)
  directionHi := (432683575251088210459/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree076.table
  base := (663268246162145514760651625775156431517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-446598353491108145604166802199803000000000000)
      constant := (8180785684431401814782741198277473828070717265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree076.table
  base := (3316320332637697439650336685622884313681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-4030620667779838050127643069154102000000000000)
      constant := (74037695762452053802905288070356135341566820761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216341787625544105229/50000000000000000000)
  centralHi := (432683575251088210459/100000000000000000000)
  directionLo := (217779290400448565969/50000000000000000000)
  directionHi := (435558580800897131939/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree077.table
  base := (3999612178222845744350578752830201274763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-452478258019437359375341036696044250000000000)
      constant := (8403221791804593836175989227608344104028620067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree077.table
  base := (1999797034169363808507736326306631403633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2041843821940820649795224944082214750000000000)
      constant := (38025250686248097553155279659518842896859796073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217779290400448565969/50000000000000000000)
  centralHi := (435558580800897131939/100000000000000000000)
  directionLo := (219207366622633805357/50000000000000000000)
  directionHi := (87682946649053522143/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree078.table
  base := (588055262101538064684657017542784430097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-114589540636941643286628817798071375000000000)
      constant := (2157171523675957885598220998156039935764940346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree078.table
  base := (188177056220432639570349720652499006649/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-459639402220382727672584078574973000000000000)
      constant := (8676744775761162003513576918985904172589011025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219207366622633805357/50000000000000000000)
  centralHi := (87682946649053522143/20000000000000000000)
  directionLo := (110313099670819545961/25000000000000000000)
  directionHi := (88250479736655636769/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree079.table
  base := (5430829201552613715117565084428470916793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-464238067076095786917689505688526750000000000)
      constant := (8857178576333800687348005084852412676215480337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree079.table
  base := (5430815607793710561908274494381335951589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-4189821596085247798516063526185084500000000000)
      constant := (80158300443478120079696314224440726058154008109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110313099670819545961/25000000000000000000)
  centralHi := (88250479736655636769/20000000000000000000)
  directionLo := (111017982879175423769/25000000000000000000)
  directionHi := (444071931516701695077/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree080.table
  base := (6178771966165543814415908309061112254739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-470117971604425000688863740184768000000000000)
      constant := (9088699222333749409460804189522958505204839251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree080.table
  base := (3089380095611817797539638350908230961019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2121444286093525523989435172597706000000000000)
      constant := (41126646815857822378551870622573989906010049939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111017982879175423769/25000000000000000000)
  centralHi := (444071931516701695077/100000000000000000000)
  directionLo := (223436837483326438257/50000000000000000000)
  directionHi := (89374734993330575303/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree081.table
  base := (6948269085615169444604163356475964831213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-475997876132754214460037974681009250000000000)
      constant := (9323248020424594686917724042430693546456258117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree081.table
  base := (6948258887547949357616979523877332682413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-477328394254317144160186351578415500000000000)
      constant := (9375075826574014456600950693878728534146323917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223436837483326438257/50000000000000000000)
  centralHi := (89374734993330575303/20000000000000000000)
  directionLo := (449657961561261854277/100000000000000000000)
  directionHi := (224828980780630927139/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree082.table
  base := (7739319444045539958211525370673673755589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-481877780661083428231212209177250500000000000)
      constant := (9560824960107247880076711840685519869803836901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree082.table
  base := (773931061287871888553639277224942771049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2174511262195328773452241991608033500000000000)
      constant := (43262733387022431042643773134792897565851001845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449657961561261854277/100000000000000000000)
  centralHi := (224828980780630927139/50000000000000000000)
  directionLo := (90485022719267030043/20000000000000000000)
  directionHi := (56553139199541893777/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree083.table
  base := (2137980521842569252705200845674061708301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-121939421297353160500596610918372937500000000)
      constant := (2450357508101177563773786558615127931671997859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree083.table
  base := (8551914440906666615388562206214940464657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-4402089500492460796367290802226394500000000000)
      constant := (88702646557911044751390290425121470209425119417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90485022719267030043/20000000000000000000)
  centralHi := (56553139199541893777/12500000000000000000)
  directionLo := (455175443570810711547/100000000000000000000)
  directionHi := (113793860892702677887/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree084.table
  base := (73328720311233278363017028770611921823/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-123409397429435463943390169542433250000000000)
      constant := (2511265807410393937786950211230792400755343424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree084.table
  base := (2346517395002696141432631943119696132591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-123754346572062890161947156145464500000000000)
      constant := (2525200603436928320301117150312291689661548719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455175443570810711547/100000000000000000000)
  centralHi := (113793860892702677887/25000000000000000000)
  directionLo := (457909254598672429849/100000000000000000000)
  directionHi := (9158185091973448597/2000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree085.table
  base := (5120890541997458928696648460841913245747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-249758747123035534772367456332987125000000000)
      constant := (5145862272627752805141673461889241478721421023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree085.table
  base := (1024177535369604665323822287389698964131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2254111726348033647646452220123524750000000000)
      constant := (46569596107106855559937680972218069220376636055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457909254598672429849/100000000000000000000)
  centralHi := (9158185091973448597/2000000000000000000)
  directionLo := (460626840798861100589/100000000000000000000)
  directionHi := (46062684079886110059/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree086.table
  base := (2779759035888500504577684111310681072447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-126349349693600070828977286790553875000000000)
      constant := (2635353493409007804631446378226353563445028823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree086.table
  base := (555951559193727086989468818743938225743/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1140322607199467636188927814814344250000000000)
      constant := (23849639495102714278852097995667354812908214915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460626840798861100589/100000000000000000000)
  centralHi := (46062684079886110059/10000000000000000000)
  directionLo := (231664243832300785903/50000000000000000000)
  directionHi := (463328487664601571807/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree087.table
  base := (1502230108593017960759990622613416007963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-127819325825682374271770845414614187500000000)
      constant := (2698532877496679383486042444095969881090191484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree087.table
  base := (12017836576576096802034888551574443652809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-512706378322185977135390897585300500000000000)
      constant := (10853924331165663255072120268025225526266779881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231664243832300785903/50000000000000000000)
  centralHi := (463328487664601571807/100000000000000000000)
  directionLo := (116503618103364705227/25000000000000000000)
  directionHi := (466014472413458820909/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree088.table
  base := (3234548705945970273910286731144460875509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-129289301957764677714564404038674500000000000)
      constant := (2762469287551824195697763212523725951127664181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree088.table
  base := (6469095554867424088824179976229594459503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2333712190500738521840662448639016000000000000)
      constant := (49999737589356544129903985700577197538425173543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116503618103364705227/25000000000000000000)
  centralHi := (466014472413458820909/100000000000000000000)
  directionLo := (234342532159668944469/50000000000000000000)
  directionHi := (468685064319337888939/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree089.table
  base := (13880097636168824649455513558082449599943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-523037112359387924629431850650939250000000000)
      constant := (11308650890792875163343191330089208430395238687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree089.table
  base := (3470023605687442950607208458331109426241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1180122839275820073286032929072089875000000000)
      constant := (25585256636135289672276114432848797495682889121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234342532159668944469/50000000000000000000)
  centralHi := (468685064319337888939/100000000000000000000)
  directionLo := (47134052502755310553/10000000000000000000)
  directionHi := (471340525027553105531/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree090.table
  base := (14843548987510598815482394116657535722167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-528917016887717138400606085147180500000000000)
      constant := (11570452728747736450219614921501132589547369303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree090.table
  base := (14843546207561198363601211485817039557967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-530395370356120393622993170588743000000000000)
      constant := (11634441450209819969607048141025262368950911503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47134052502755310553/10000000000000000000)
  centralHi := (471340525027553105531/100000000000000000000)
  directionLo := (236990554427005031731/50000000000000000000)
  directionHi := (473981108854010063463/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree091.table
  base := (7914274302851116879983506530794865279149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-267398460708023176085890159821710875000000000)
      constant := (5917641330755813082127262470643461085653700441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree091.table
  base := (3957136550255730623766799125445796049933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1206656327326721698017436338577253625000000000)
      constant := (26776578669617816888819582044128009070538751373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236990554427005031731/50000000000000000000)
  centralHi := (473981108854010063463/100000000000000000000)
  directionLo := (119151765767367160139/25000000000000000000)
  directionHi := (476607063069468640557/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree092.table
  base := (16835096258217747535056402676138000486167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-540676825944375565942954554139663000000000000)
      constant := (12103140686896707341300572816199760790324345303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree092.table
  base := (8417547089190804797333126826825942103521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2439846142704345020766276086659671000000000000)
      constant := (54765025702628742524051793084821638040768261801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119151765767367160139/25000000000000000000)
  centralHi := (476607063069468640557/100000000000000000000)
  directionLo := (479218628169786384003/100000000000000000000)
  directionHi := (119804657042446596001/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree093.table
  base := (8931595873190785734832731565653942898917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-273278365236352389857064394317952125000000000)
      constant := (6187013401516820777865759420974319787603097553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree093.table
  base := (17863189947702613727858710143752736775789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-548084362390054810110595443592185500000000000)
      constant := (12442353690665979383617383690715728148760898701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479218628169786384003/100000000000000000000)
  centralHi := (119804657042446596001/25000000000000000000)
  directionLo := (481816038132978198541/100000000000000000000)
  directionHi := (240908019066489099271/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree094.table
  base := (4728208725116830513697562614083276677103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-138109158750258498371325755783036375000000000)
      constant := (3161985252081368316277786227428154649864237127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree094.table
  base := (18912833345104731255224705369514639664233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-4985826237612296540458165811339997000000000000)
      constant := (114459710096802631563247216101220544545156914673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481816038132978198541/100000000000000000000)
  centralHi := (240908019066489099271/50000000000000000000)
  directionLo := (15137485020745937627/3125000000000000000)
  directionHi := (96879904132774000813/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree095.table
  base := (19984025575505804713122126443681858265427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-558316539529363207256477257628386750000000000)
      constant := (12924883301408187317661554042597031110278777643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree095.table
  base := (1998402423068641232593928217038366384057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2519446606857049894960486315175162250000000000)
      constant := (58482816017918466618629083313333691218060404085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15137485020745937627/3125000000000000000)
  centralHi := (96879904132774000813/20000000000000000000)
  directionLo := (486969297427070390233/100000000000000000000)
  directionHi := (243484648713535195117/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree096.table
  base := (21076763647699554223754692770829809072763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-564196444057692421027651492124628000000000000)
      constant := (13204853681116973363119237938785245673565627067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree096.table
  base := (21076762485043035338949752155495173326193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-565773354423989226598197716595628000000000000)
      constant := (13277661002553935190310062454128362085826149937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486969297427070390233/100000000000000000000)
  centralHi := (243484648713535195117/50000000000000000000)
  directionLo := (48952558426893488169/10000000000000000000)
  directionHi := (489525584268934881691/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree097.table
  base := (22191049011356105027820140871212903057707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (168)
      previous := (84)
      next := (84)
      square := (650272315998682709503597720000000000000)
      linear := (-60588409882667832373134841813250000000000)
      constant := (1433505382767283557555617960194968762432707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree097.table
  base := (11095524003144721885444229164855421009041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (756)
      previous := (378)
      next := (378)
      square := (2926225421994072192766189740000000000000)
      linear := (-273409882342316201979306316737750000000000)
      constant := (6486324851186116752592682852624023007831369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48952558426893488169/10000000000000000000)
  centralHi := (489525584268934881691/100000000000000000000)
  directionLo := (492068591429151864363/100000000000000000000)
  directionHi := (123017147857287966091/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree098.table
  base := (5831720394066227703596389634363451282923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-143989063278587712142499990279277625000000000)
      constant := (3443469674145147294296675154426366000230397507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree098.table
  base := (23326880707514413844702215355365632942863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-5198094142019509538309393087381307000000000000)
      constant := (124647768108381988909089157339659388006984581703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492068591429151864363/100000000000000000000)
  centralHi := (123017147857287966091/25000000000000000000)
  directionLo := (494598523742537174539/100000000000000000000)
  directionHi := (24729926187126858727/5000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree099.table
  base := (4896852253090742290231733938253728201631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-581836157642680062341174195613351750000000000)
      constant := (14062933330762395919972173603857681445980105395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree099.table
  base := (12242130257302187779133635533155372444829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-291731173228961821542899994799535250000000000)
      constant := (7070181677388574281546715271495287848552146061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494598523742537174539/100000000000000000000)
  centralHi := (24729926187126858727/5000000000000000000)
  directionLo := (124278895207896378439/25000000000000000000)
  directionHi := (497115580831585513757/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree100.table
  base := (6415797003317361322389852770547593299191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-146929015542752319028087107527398250000000000)
      constant := (3588754012096265391086434632701867266289588119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree100.table
  base := (12831593682191406693642357526071201010371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2652114047111558018617503362700981000000000000)
      constant := (64953083649053769507715551264991421310259226651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124278895207896378439/25000000000000000000)
  centralHi := (497115580831585513757/100000000000000000000)
  directionLo := (124904989322572737299/25000000000000000000)
  directionHi := (499619957290290949197/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree101.table
  base := (26863661763736755720626803117890478691167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-593595966699338489883522664605834250000000000)
      constant := (14650126848921913979973681541570607785489565303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree101.table
  base := (13431830601509776281370961642636023899751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2678647535162459643348906772206144750000000000)
      constant := (66288229709581600861122541126791072745323564431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124904989322572737299/25000000000000000000)
  centralHi := (499619957290290949197/100000000000000000000)
  directionLo := (502111842859715542197/100000000000000000000)
  directionHi := (251055921429857771099/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree102.table
  base := (28085682469153938689249180728155565588379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-599475871227667703654696899102075500000000000)
      constant := (14948265731924127833401456979501459802558558011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree102.table
  base := (14042840992335392596084365926964632619033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-300575669245929029786701131301256500000000000)
      constant := (7515230364015512538452252672638914400187481497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502111842859715542197/100000000000000000000)
  centralHi := (251055921429857771099/50000000000000000000)
  directionLo := (252295711297877195623/50000000000000000000)
  directionHi := (504591422595754391247/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree103.table
  base := (7332312522222997552938338463412191500321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-151338943938999229356467783399579187500000000)
      constant := (3812358174252356206536670949832931131603864039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree103.table
  base := (14664624835158186218980877210159436923339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2731714511264262892811713591216472250000000000)
      constant := (68999614347075673274105203866633475039824019859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252295711297877195623/50000000000000000000)
  centralHi := (504591422595754391247/100000000000000000000)
  directionLo := (63382359628689609471/12500000000000000000)
  directionHi := (507058877029516875769/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree104.table
  base := (3824295573545922863523258789989333366211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-152808920071081532799261342023639500000000000)
      constant := (3888406935963102137272845462837987744035358598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree104.table
  base := (3059436422676581521203984591946940745537/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2758247999315164517543117000721636000000000000)
      constant := (70375852920984479818588430842817384696364093485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63382359628689609471/12500000000000000000)
  centralHi := (507058877029516875769/100000000000000000000)
  directionLo := (127378595580179364343/25000000000000000000)
  directionHi := (509514382320717457373/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree105.table
  base := (7970256484540862610823458439188372580857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-154278896203163836242054900647699812500000000)
      constant := (3965212718044074397171787747053732360015627263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree105.table
  base := (3188102562580843658123897992810161482319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-309420165262896238030502267802977750000000000)
      constant := (7973976555185730923647924835725233714904447355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127378595580179364343/25000000000000000000)
  centralHi := (509514382320717457373/100000000000000000000)
  directionLo := (255979055202222433609/50000000000000000000)
  directionHi := (511958110404444867219/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree106.table
  base := (331892341132788930646287097370928319099/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-155748872335246139684848459271760125000000000)
      constant := (4042775520436463678890802148724083916594437275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree106.table
  base := (33189233843486866956718967046819084010071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-5622629950833935534011847639463927000000000000)
      constant := (146338845146245203499515187726994974946806822351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255979055202222433609/50000000000000000000)
  centralHi := (511958110404444867219/100000000000000000000)
  directionLo := (257195114565827864077/50000000000000000000)
  directionHi := (102878045826331145631/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree107.table
  base := (862974727312125635794973093495294999979/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-157218848467328443127642017895820437500000000)
      constant := (4121095343090334807337952116231735796294117860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree107.table
  base := (862974721486898896254227254771120558483/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1418924231733934695868663614618563625000000000)
      constant := (37293376824738486547558460976000268277863364230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257195114565827864077/50000000000000000000)
  centralHi := (102878045826331145631/20000000000000000000)
  directionLo := (258405451201858744209/50000000000000000000)
  directionHi := (516810902403717488419/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree108.table
  base := (35870290857776045967095949118940813230333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-634755298397642986281742306079523000000000000)
      constant := (16800688743853334543008291071094824205434203197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree108.table
  base := (35870290656551826427405046041212785895743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-636529322559726892548606808609398000000000000)
      constant := (16892840494445649953735894953857681977493045887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258405451201858744209/50000000000000000000)
  centralHi := (516810902403717488419/100000000000000000000)
  directionLo := (10384405806026117051/2000000000000000000)
  directionHi := (519220290301305852551/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree109.table
  base := (9310784848474720063926753358240441007869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-160158800731493050013229135143941062500000000)
      constant := (4280006049019581119840920759374433713251633171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree109.table
  base := (18621569610069002635822621547639823612263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2890915439569672641200134048247454750000000000)
      constant := (77462508299090781667138168909556914696278793103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10384405806026117051/2000000000000000000)
  centralHi := (519220290301305852551/100000000000000000000)
  directionLo := (521618549207943568403/100000000000000000000)
  directionHi := (130404637301985892101/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree110.table
  base := (7727506937590219068263913874651353132209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-646515107454301413824090775072005500000000000)
      constant := (17442387728914910046732039606508889431542272405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree110.table
  base := (19318767268958727180695414635020559059931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2917448927620574265931537457752618500000000000)
      constant := (78920931871211534172747574656972130883629017011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521618549207943568403/100000000000000000000)
  centralHi := (130404637301985892101/25000000000000000000)
  directionLo := (131001457982112590163/25000000000000000000)
  directionHi := (524005831928450360653/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree111.table
  base := (40053476729037044763735637070725962675363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-652395011982630627595265009568246750000000000)
      constant := (17767779342260574107569357985539927401171865467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree111.table
  base := (20026738299750475994978313850556472263151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-327109157296830654518104540806420250000000000)
      constant := (8932561437880866385218648978175417327992737759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131001457982112590163/25000000000000000000)
  centralHi := (524005831928450360653/100000000000000000000)
  directionLo := (526382287802557893909/100000000000000000000)
  directionHi := (52638228780255789391/10000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree112.table
  base := (41490965507973826616126984485984783288283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-658274916510959841366439244064488000000000000)
      constant := (18096199036028914737834291339332279325959454747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree112.table
  base := (41490965396143654126292185091466098102727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-5941031807444755030788688553525892000000000000)
      constant := (163757743015738620962204551263107864653437025087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526382287802557893909/100000000000000000000)
  centralHi := (52638228780255789391/10000000000000000000)
  directionLo := (52874806281392881379/10000000000000000000)
  directionHi := (528748062813928813791/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree113.table
  base := (2684375063564990849810755786284570467701/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-166038705259822263784403369640182312500000000)
      constant := (4606911702536819880651705923813221486212238586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree113.table
  base := (171800003682011406617255138082853489307/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-2997049391773279140125747686268109750000000000)
      constant := (83378387571725179239821336524630005490219508375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52874806281392881379/10000000000000000000)
  centralHi := (528748062813928813791/100000000000000000000)
  directionLo := (531103299694805070771/100000000000000000000)
  directionHi := (132775824923701267693/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree114.table
  base := (111076458124399686950164479672225145619/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-167508681391904567227196928264242625000000000)
      constant := (4690530666138685706480572653403073145372292100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree114.table
  base := (8886116633286190236959788302203054797491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-671907306627595725523811354616283000000000000)
      constant := (18864800251607802570050810861949558306697964095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531103299694805070771/100000000000000000000)
  centralHi := (132775824923701267693/25000000000000000000)
  directionLo := (533448138026497805023/100000000000000000000)
  directionHi := (16670254313328056407/3125000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree115.table
  base := (22966356100360589546053411916968221996039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-337957315047973741339980973776605875000000000)
      constant := (9549813299600188224646000276511744933377918451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree115.table
  base := (45932712128798572626533927084291446941357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-6100232735750164779177109010556874500000000000)
      constant := (172837024378363853879144355604373083354378552117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533448138026497805023/100000000000000000000)
  centralHi := (16670254313328056407/3125000000000000000)
  directionLo := (535782714335918992443/100000000000000000000)
  directionHi := (133945678583979748111/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree116.table
  base := (4745638786541647204739090123893676010761/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-340897267312138348225568091024726500000000000)
      constant := (9720079307020885629449980937437922534801251245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree116.table
  base := (47456387803343396727759632917453729962159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-6153299711851968028639915829567202000000000000)
      constant := (175918241484770313269145633537833758181925586279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535782714335918992443/100000000000000000000)
  centralHi := (133945678583979748111/25000000000000000000)
  directionLo := (10762143243766875203/2000000000000000000)
  directionHi := (538107162188343760151/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree117.table
  base := (4900161024010956876429067887374488452223/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-343837219576302955111155208272847125000000000)
      constant := (9891859354521886745597471444043546663727018535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree117.table
  base := (49001610186541028557278643470616395767189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-689596298661530142011413627619725500000000000)
      constant := (19891872620376794668143600356954998441210981301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10762143243766875203/2000000000000000000)
  centralHi := (538107162188343760151/100000000000000000000)
  directionLo := (270210806138290858171/50000000000000000000)
  directionHi := (540421612276581716343/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree118.table
  base := (50568379321720603602605671886769745366167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-693554343680935123993484651041935500000000000)
      constant := (20130306884177404690368297230688614245087765303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree118.table
  base := (25284189637747341972786075452519224052819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-3129716832027787263782764733793928500000000000)
      constant := (91081430336990533765662821231032170208891765739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270210806138290858171/50000000000000000000)
  centralHi := (540421612276581716343/100000000000000000000)
  directionLo := (271363096253362875903/50000000000000000000)
  directionHi := (542726192506725751807/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree119.table
  base := (26078347553863966766381190877191725159197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-349717124104632168882329442769088375000000000)
      constant := (10239961569709469358577383927535796491827572073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree119.table
  base := (13039173766960242137396340620254766557671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1578125160039344444257084071649546125000000000)
      constant := (46331565689084981306720282095562804080229512951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271363096253362875903/50000000000000000000)
  centralHi := (542726192506725751807/100000000000000000000)
  directionLo := (545021028080637509921/100000000000000000000)
  directionHi := (272510514040318754961/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree120.table
  base := (53766557596084320223989352865676020019069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-705314152737593551535833120034418000000000000)
      constant := (20832567474749113106100126135392977547359420221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree120.table
  base := (13441639390417353702385057886889785300753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-176821322673866139624753975155792000000000000)
      constant := (5236584995286276244348036005686176614894784977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545021028080637509921/100000000000000000000)
  centralHi := (272510514040318754961/50000000000000000000)
  directionLo := (109461248315064008799/20000000000000000000)
  directionHi := (136826560393830010999/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree121.table
  base := (1107959335702906495600650093249600326201/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-355597028632961382653503677265329625000000000)
      constant := (10594119945076227665814758713840485255285317725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree121.table
  base := (5539796675545378035131423656837540621903/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-3209317296180492137976974962309419750000000000)
      constant := (95867625947874941254893538341601881273735589715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109461248315064008799/20000000000000000000)
  centralHi := (136826560393830010999/25000000000000000000)
  directionLo := (137395488254830011029/25000000000000000000)
  directionHi := (549581953019320044117/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree122.table
  base := (11410184534721629515469821736489836683651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-717073961794251979078181589026900500000000000)
      constant := (21546940385616707352085028199833355952719861295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree122.table
  base := (57050922647993400662451505586312555399707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-6471701568462787525416756743629167000000000000)
      constant := (194980838952570064895075194124551561097552588467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137395488254830011029/25000000000000000000)
  centralHi := (549581953019320044117/100000000000000000000)
  directionLo := (275924139983147191143/50000000000000000000)
  directionHi := (551848279966294382287/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree123.table
  base := (29362712630229700529537797761838183120071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-361476933161290596424677911761570875000000000)
      constant := (10954334480566167101972064563673794725718935539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree123.table
  base := (2349017009534525449490116536664166811241/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-724974282729398974986618173626610500000000000)
      constant := (22028202333409794468212393434330505411611664225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275924139983147191143/50000000000000000000)
  centralHi := (551848279966294382287/100000000000000000000)
  directionLo := (138526334391467139911/25000000000000000000)
  directionHi := (110821067513173711929/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree124.table
  base := (15105368636232630460349067503051409915939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-182208442712727601655132514504845750000000000)
      constant := (5568356404173026118582124583582979926836570051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree124.table
  base := (60421474525870665919819643355412262547453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-6577835520666394024342370381649822000000000000)
      constant := (201554198040045512018493449339175020679780867493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138526334391467139911/25000000000000000000)
  centralHi := (110821067513173711929/20000000000000000000)
  directionLo := (111270647726381582113/20000000000000000000)
  directionHi := (278176619315953955283/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree125.table
  base := (62139070526459715428807660268606838056051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-734713675379239620391704292515624250000000000)
      constant := (22641210352290732238829943653872788292003758859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree125.table
  base := (12427814102004011813175589397605720708989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-6630902496768197273805177200660149500000000000)
      constant := (204881970070600154405933174125647069512726987545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111270647726381582113/20000000000000000000)
  centralHi := (278176619315953955283/50000000000000000000)
  directionLo := (558592093708316095643/100000000000000000000)
  directionHi := (139648023427079023911/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree126.table
  base := (63878213204659486771802276720521078615349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-740593579907568834162878527011865500000000000)
      constant := (23012023167924571556527649116583870477129318741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree126.table
  base := (63878213190480713834294174940436879984393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-742663274763333391474220446630053000000000000)
      constant := (23137459676924897964635741856194402197523153737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558592093708316095643/100000000000000000000)
  centralHi := (139648023427079023911/25000000000000000000)
  directionLo := (70102751391558683931/12500000000000000000)
  directionHi := (560822011132469471449/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree127.table
  base := (2625556103171557869438287610654412724219/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-746473484435898047934052761508106750000000000)
      constant := (23385864063591355901555829382548324363913789275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree127.table
  base := (65638902567060881203388092280646750516271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-6737036448971803772730790838680804500000000000)
      constant := (211619699105201056346954053105206797378905844551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70102751391558683931/12500000000000000000)
  centralHi := (560822011132469471449/100000000000000000000)
  directionLo := (563043097096390333933/100000000000000000000)
  directionHi := (281521548548195166967/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree128.table
  base := (16855284662557550405658261821492019577989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-188088347241056815426306749001087000000000000)
      constant := (5940683259822494003025996693388524412209298501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree128.table
  base := (16855284659921276857807379699417524725129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1697525856268401755548399414422783000000000000)
      constant := (53757414027306172225827478433392979411248648849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563043097096390333933/100000000000000000000)
  centralHi := (281521548548195166967/50000000000000000000)
  directionLo := (282627727852878385451/50000000000000000000)
  directionHi := (565255455705756770903/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree129.table
  base := (13844984283493646608687240317659549649011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-758233293492556475476401230500589250000000000)
      constant := (24142630095020290580155725472589632769097097495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree129.table
  base := (69224921408375024418409343656410673761281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-760352266797267807961822719633495500000000000)
      constant := (24274112011599645684640355075135354990357392929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282627727852878385451/50000000000000000000)
  centralHi := (565255455705756770903/100000000000000000000)
  directionLo := (567459189036841905233/100000000000000000000)
  directionHi := (283729594518420952617/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree130.table
  base := (17762562720268440286412971611618175392993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-191028299505221422311893866249207625000000000)
      constant := (6131388807695741252894213059880436886882046137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree130.table
  base := (17762562718308250039869988084760675586823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1724059344319303380279802823927946750000000000)
      constant := (55482938772681522936615147372040406230305258463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567459189036841905233/100000000000000000000)
  centralHi := (283729594518420952617/50000000000000000000)
  directionLo := (22786175887658825771/4000000000000000000)
  directionHi := (142413599297867661069/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree131.table
  base := (72897127041188657503481915637188556437137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-769993102549214903018749699493071750000000000)
      constant := (24911508446579334176009031940175371055251397033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree131.table
  base := (72897127034428232214670658879463176386453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-6949304353379016770582018114722114500000000000)
      constant := (225423897068226858475999873711106638825518726493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22786175887658825771/4000000000000000000)
  centralHi := (142413599297867661069/25000000000000000000)
  directionLo := (2287364713400310613/400000000000000000)
  directionHi := (571841178350077653251/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree132.table
  base := (74765549898013536717689252084919912538313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-775873007077544116789923933989313000000000000)
      constant := (25300489742411285656230843292706884800822987017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree132.table
  base := (37382774946092463815952427650624418175247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-389020629415601112224712496318469000000000000)
      constant := (12719079668717672079300347172500096588110899023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2287364713400310613/400000000000000000)
  centralHi := (571841178350077653251/100000000000000000000)
  directionLo := (17938113400717066383/3125000000000000000)
  directionHi := (574019628822946124257/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree133.table
  base := (76655519451797209433492431976609373074351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-781752911605873330561098168485554250000000000)
      constant := (25692499118281160511603147504099231737740943559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree133.table
  base := (19163879861693066121124412414299477359361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1763859576395655817376907938185692375000000000)
      constant := (58122591499205650717276528083716482720002423841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17938113400717066383/3125000000000000000)
  centralHi := (574019628822946124257/100000000000000000000)
  directionLo := (576189843099703001367/100000000000000000000)
  directionHi := (72023730387462875171/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree134.table
  base := (1227609932856683209401226594319382498889/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-196908204033550636083068100745448875000000000)
      constant := (6521884143547917250557774974245063702897120616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree134.table
  base := (78567035698495874431169333780991740789993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7108505281684426518970438571753097000000000000)
      constant := (236064692947966255995591556433467185695587397233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576189843099703001367/100000000000000000000)
  centralHi := (72023730387462875171/12500000000000000000)
  directionLo := (578351913897142631337/100000000000000000000)
  directionHi := (289175956948571315669/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree135.table
  base := (16100019730284954898068055102365488973793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-793512720662531758103446637478036750000000000)
      constant := (26485602110145819090083585751194874340881466685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree135.table
  base := (80500098647690623537348847209215950312957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-795730250865136640937027265640380500000000000)
      constant := (26629601654486379288905463269967012212432112413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578351913897142631337/100000000000000000000)
  centralHi := (289175956948571315669/50000000000000000000)
  directionLo := (290252966102723662357/50000000000000000000)
  directionHi := (116101186441089464943/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree136.table
  base := (10306838537241655895267844075474298522479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-199848156297715242968655217993569500000000000)
      constant := (6721673931536713962380955013408631568346009822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree136.table
  base := (82454708294714500948177798608947114228993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7214639233888033017896052209773752000000000000)
      constant := (243295531824086390561578687887110415080025356233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290252966102723662357/50000000000000000000)
  centralHi := (116101186441089464943/20000000000000000000)
  directionLo := (582651987332870020637/100000000000000000000)
  directionHi := (291325993666435010319/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree137.table
  base := (42215432321358892342009962678624715594431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-402636264859595092822897553235259625000000000)
      constant := (13645408711099105095116192367724875561332688779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree137.table
  base := (3377234585597738106711346637947385174383/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7267706209989836267358859028784079500000000000)
      constant := (246952043749125022363455630767539598622235670575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582651987332870020637/100000000000000000000)
  centralHi := (291325993666435010319/50000000000000000000)
  directionLo := (584790166948941138321/100000000000000000000)
  directionHi := (292395083474470569161/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree138.table
  base := (4321428384307908696690003254923253437307/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-202788108561879849854242335241690125000000000)
      constant := (6924491799575863881735691500387361698192482815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree138.table
  base := (86428567683767021354972556888624159296563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-813419242899071057424629538643823000000000000)
      constant := (27848438962836255096407817563751521058571361267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584790166948941138321/100000000000000000000)
  centralHi := (292395083474470569161/50000000000000000000)
  directionLo := (586920557126258757889/100000000000000000000)
  directionHi := (58692055712625875789/10000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree139.table
  base := (44223908714322731355660388627439974919339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-408516169387924306594071787731500875000000000)
      constant := (14054072527233135614201817940700191766008248151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree139.table
  base := (88447817426584673272925272788880555810309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7373840162193442766284472666804734500000000000)
      constant := (254347252573324038276855283245758573557510276429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586920557126258757889/100000000000000000000)
  centralHi := (58692055712625875789/10000000000000000000)
  directionLo := (294521621190459246201/50000000000000000000)
  directionHi := (589043242380918492403/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree140.table
  base := (90488613870578689463375702718960862485767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-822912243304177826959317809959243000000000000)
      constant := (28521350990690411847360875742159781348878581703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree140.table
  base := (90488613868802710826152863472039761464441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7426907138295246015747279485815062000000000000)
      constant := (258085949472552655684926806493550650915570328321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294521621190459246201/50000000000000000000)
  centralHi := (589043242380918492403/100000000000000000000)
  directionLo := (147789576427909195483/25000000000000000000)
  directionHi := (591158305711636781933/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree141.table
  base := (92550957012362136731479539682911682716371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-828792147832507040730492044455484250000000000)
      constant := (28937585006979681278247597379118086512912709739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree141.table
  base := (92550957010831683906398483449689290239139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-831108234933005473912231811647265500000000000)
      constant := (29094671262582990429696403320481740430297558851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147789576427909195483/25000000000000000000)
  centralHi := (591158305711636781933/100000000000000000000)
  directionLo := (593265828637618850169/100000000000000000000)
  directionHi := (59326582863761885017/10000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree142.table
  base := (94634846854403030804691370859934908893819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-834672052360836254501666278951725500000000000)
      constant := (29356847103337911113217557701523821331219442971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree142.table
  base := (2957338964158882059794357070870814513623/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1883260272624713128668223280958929250000000000)
      constant := (66411382061360438758200650198221391261562374104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593265828637618850169/100000000000000000000)
  centralHi := (59326582863761885017/10000000000000000000)
  directionLo := (595365891235220206007/100000000000000000000)
  directionHi := (74420736404402525751/12500000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree143.table
  base := (24185070849277405332023932275202815350257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-210137989222291367068210128361991687500000000)
      constant := (7444784319942235643295339269742495400470411863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree143.table
  base := (96740283395973251127144046279890273486229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7586108066600655764135699942846044500000000000)
      constant := (269466410119172145175670332194193861397524857949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595365891235220206007/100000000000000000000)
  centralHi := (74420736404402525751/12500000000000000000)
  directionLo := (597458572173448338781/100000000000000000000)
  directionHi := (298729286086724169391/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree144.table
  base := (49433633320444792128045335190180701850289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-423215930708747341022007373972104000000000000)
      constant := (15102227768138305740596963410061827473709369201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree144.table
  base := (193100130156075115918203401721893670219/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-212199306741734972599958521162677000000000000)
      constant := (7592074638457581873523621505202309085515593088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597458572173448338781/100000000000000000000)
  centralHi := (298729286086724169391/50000000000000000000)
  directionLo := (149885987187087284759/25000000000000000000)
  directionHi := (599543948748349139037/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree145.table
  base := (50507898293074349891872124768568446711071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-426155882972911947907594491220224625000000000)
      constant := (15316400936432367911555331126480386486784154539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree145.table
  base := (101015796585305101640559164219951202308183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7692242018804262263061313580866699500000000000)
      constant := (277190358841378817635203130717534911161096744623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149885987187087284759/25000000000000000000)
  centralHi := (599543948748349139037/100000000000000000000)
  directionLo := (601622096916320569983/100000000000000000000)
  directionHi := (4700172632158754453/781250000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree146.table
  base := (103185873233289763940548823623115706686813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-858191670474153109586363216936690500000000000)
      constant := (31064176289537105506773056964983396457653723517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree146.table
  base := (25796468308140741927715732537969330190793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-1936327248726516378131030099969256750000000000)
      constant := (70273356422481029604841124996851255685824042033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601622096916320569983/100000000000000000000)
  centralHi := (4700172632158754453/781250000000000000)
  directionLo := (120738618265278842341/20000000000000000000)
  directionHi := (301846545663197105853/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree147.table
  base := (105377496582711698561246967911578559019053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-864071575002482323357537451432931750000000000)
      constant := (31498578786297473987724203846937823652044644677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree147.table
  base := (105377496582085561340407781696438077014273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-866486219000874306887436357654150500000000000)
      constant := (31669320836682538837875094448038316515064794657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120738618265278842341/20000000000000000000)
  centralHi := (301846545663197105853/50000000000000000000)
  directionLo := (605757005351523494641/100000000000000000000)
  directionHi := (302878502675761747321/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree148.table
  base := (107590666634808829505467934456811799711479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-869951479530811537128711685929173000000000000)
      constant := (31936009363149551477977354531402834817235305911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree148.table
  base := (21518133326853887017324028845054763008317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7851442947109672011449734037897682000000000000)
      constant := (288981744362068591466852607979250264806536459385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605757005351523494641/100000000000000000000)
  centralHi := (302878502675761747321/50000000000000000000)
  directionLo := (60781391111891572537/10000000000000000000)
  directionHi := (607813911118915725371/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree149.table
  base := (27456345847492576851964719992552473902937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-218957846014785187724971480106353562500000000)
      constant := (8094117005024249873963476028968985122948827983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree149.table
  base := (109825383389505659796506015492736064621291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-7904509923211475260912540856908009500000000000)
      constant := (292966996185734460467690088723957513149133043171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60781391111891572537/10000000000000000000)
  centralHi := (607813911118915725371/100000000000000000000)
  directionLo := (609863879539443380839/100000000000000000000)
  directionHi := (15246596988486084521/2500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree150.table
  base := (5604082342428982450558376965701190927011/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-220427822146867491167765038730413875000000000)
      constant := (8204988689285856637596591509419015017395607495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree150.table
  base := (56040823424089704012852625132816862330597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-442087605517404361687519315328796500000000000)
      constant := (16498869055620726296698468378220818779543587173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609863879539443380839/100000000000000000000)
  centralHi := (15246596988486084521/2500000000000000000)
  directionLo := (1195130820969079301/195312500000000000)
  directionHi := (611906980336168602113/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree151.table
  base := (22871891402202876071739146585490072518351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-887591193115799178442234389417896750000000000)
      constant := (33266469574292384784116167125315596186235197795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree151.table
  base := (114359457010669633552696491414743001868513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-8010643875415081759838154494928664500000000000)
      constant := (301019684808416520270414984188242139414665049353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1195130820969079301/195312500000000000)
  centralHi := (611906980336168602113/100000000000000000000)
  directionLo := (122788656414402670149/20000000000000000000)
  directionHi := (306971641036006675373/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree152.table
  base := (116658813877645765878725140909041097743609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-893471097644128392213408623914138000000000000)
      constant := (33716012471547367424049009706841820563669617081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree152.table
  base := (116658813877348831807981807276292905765659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-8063710851516885009300961313938992000000000000)
      constant := (305087121607496344542768094513539926053141769779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122788656414402670149/20000000000000000000)
  centralHi := (306971641036006675373/50000000000000000000)
  directionLo := (307986426088303147857/50000000000000000000)
  directionHi := (123194570435321259143/20000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree153.table
  base := (118979717448838609749537343203061617714249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-899351002172457605984582858410379250000000000)
      constant := (34168583448911806912698345167950328173182743841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree153.table
  base := (118979717448582868286929406086210084290291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-901864203068743139862640903661035500000000000)
      constant := (34353550377604836445960559669499400269024848019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307986426088303147857/50000000000000000000)
  centralHi := (123194570435321259143/20000000000000000000)
  directionLo := (154498939243084043103/25000000000000000000)
  directionHi := (617995756972336172413/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree154.table
  base := (121322167724951117947365678171025486174821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-905230906700786819755757092906620500000000000)
      constant := (34624182506389073610094552989284600135356390789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree154.table
  base := (24264433544946172787207073306954560994267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-8169844803720491508226574951959647000000000000)
      constant := (313304180181288481403916046163677622491527619135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154498939243084043103/25000000000000000000)
  centralHi := (617995756972336172413/100000000000000000000)
  directionLo := (620012061699640093687/100000000000000000000)
  directionHi := (77501507712455011711/12500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree155.table
  base := (7730385294145925693783107448204448669239/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-227777702807279008381732831850715437500000000)
      constant := (8770702410995618743457373009143310791736572754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree155.table
  base := (123686164706145128143219534098348502563561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-8222911779822294757689381770969974500000000000)
      constant := (317453801956061038624859562362873257006522409041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620012061699640093687/100000000000000000000)
  centralHi := (77501507712455011711/12500000000000000000)
  directionLo := (62202183054155409273/10000000000000000000)
  directionHi := (622021830541554092731/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree156.table
  base := (63035854196667239871734325415996146785313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-458495357878722623649052780949551500000000000)
      constant := (17772232430847627569020850298991465416978010017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree156.table
  base := (126071708393171131364051014447077935112391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-919553195102677556350243176664478000000000000)
      constant := (35736757635865606051124848117814966166472486919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62202183054155409273/10000000000000000000)
  centralHi := (622021830541554092731/100000000000000000000)
  directionLo := (78003140830944004429/12500000000000000000)
  directionHi := (624025126647552035433/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree157.table
  base := (64239399393144087410322952655570156353199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-461435310142887230534639898197672125000000000)
      constant := (18004574079765297412033817553343914314994436891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree157.table
  base := (12847879878614751061227215436712884676227/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-4164522866012950628307497704495314750000000000)
      constant := (162917615240752702515334486962130704354306642935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78003140830944004429/12500000000000000000)
  centralHi := (624025126647552035433/100000000000000000000)
  directionLo := (156505503039174488109/25000000000000000000)
  directionHi := (626022012156697952437/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree158.table
  base := (130907435885527227363348745564474171280789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-928750524814103674840454030891585500000000000)
      constant := (36476859537491611525580677419838672376018443701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree158.table
  base := (130907435885406102064388137367545321500047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-8382112708127704506077802228000957000000000000)
      constant := (330067037232233990555758220399382758713695480007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156505503039174488109/25000000000000000000)
  centralHi := (626022012156697952437/100000000000000000000)
  directionLo := (125602509644027161129/20000000000000000000)
  directionHi := (314006274110067902823/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree159.table
  base := (133357619691376292178779551013788484140711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-934630429342432888611628265387826750000000000)
      constant := (36947598995581359919661794725415127603139324799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree159.table
  base := (5334304787650879835993496437778871198639/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-937242187136611972837845449667920500000000000)
      constant := (37147359886111526666319599962013305688637358775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125602509644027161129/20000000000000000000)
  centralHi := (314006274110067902823/50000000000000000000)
  directionLo := (314998397511469858743/50000000000000000000)
  directionHi := (629996795022939717487/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree160.table
  base := (4244667193879794099163286046055418323543/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-235127583467690525595700624971017000000000000)
      constant := (9355341633450708115651809955990403448049728696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree160.table
  base := (135829350204063609242098074663949966568797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-8488246660331311005003415866021612000000000000)
      constant := (338612835709841617234456760649824367119012298757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314998397511469858743/50000000000000000000)
  centralHi := (629996795022939717487/100000000000000000000)
  directionLo := (315987405902673375641/50000000000000000000)
  directionHi := (631974811805346751283/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree161.table
  base := (34580656856042523149728127309834707634301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1529603055307901403429837736870000000000000)
      linear := (-236597559599772829038494183595077312500000000)
      constant := (9474540538039740033890554036814234671845981859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree161.table
  base := (138322627424092773700608750344119123915487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (14226408)
      previous := (7113204)
      next := (7113204)
      square := (55065709991084450523474158527320000000000000)
      linear := (-8541313636433114254466222685031939500000000000)
      constant := (342926827436774028481018175308678455680724854647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315987405902673375641/50000000000000000000)
  centralHi := (631974811805346751283/100000000000000000000)
  directionLo := (633946656883393435119/100000000000000000000)
  directionHi := (7924333211042417939/1250000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree162.table
  base := (140837451351731403084023887271955843337969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-952270142927420529925150968876550500000000000)
      constant := (38377985850652613310431290663959583178404450321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree162.table
  base := (70418725675832417277243566525772371397459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-477465589585273194662723861335681500000000000)
      constant := (19292678564212601704452311620589658289353691731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633946656883393435119/100000000000000000000)
  centralHi := (7924333211042417939/1250000000000000000)
  directionLo := (19872262114655511477/3125000000000000000)
  directionHi := (127182477533795273453/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree163.table
  base := (71686910993568034895731264017927345583643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-479075023727874871848162601686395875000000000)
      constant := (19430418814643301355545109981798744920963684487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree163.table
  base := (35843455496769689770077221030497068996157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-2161861897159180188347959080763148625000000000)
      constant := (87909248966756335169943691453301040821147945917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19872262114655511477/3125000000000000000)
  centralHi := (127182477533795273453/20000000000000000000)
  directionLo := (637872060689356426429/100000000000000000000)
  directionHi := (63787206068935642643/10000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree164.table
  base := (145931739330676590466486376470380346999123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-964029951984078957467499437869033000000000000)
      constant := (39346717488063680448824136050104955528664748307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree164.table
  base := (36482934832656812979821687449477921351053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-2175128641184631000713660785515730500000000000)
      constant := (89008293142598586250410045450251829826678519093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637872060689356426429/100000000000000000000)
  centralHi := (63787206068935642643/10000000000000000000)
  directionLo := (19994554112691416649/3125000000000000000)
  directionHi := (639825731606125332769/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree165.table
  base := (148511203382639349486661701735920877236909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-969909856512408171238673672365274250000000000)
      constant := (39835625426986541114241559950012071555406451781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree165.table
  base := (74255601691298437857001303855041292846983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-486310085602240402906524997837402750000000000)
      constant := (20025374681442117225381907395204130536116013047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19994554112691416649/3125000000000000000)
  centralHi := (639825731606125332769/100000000000000000000)
  directionLo := (320886727616826281817/50000000000000000000)
  directionHi := (128354691046730512727/20000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree166.table
  base := (75556107071652369164312447964200151340523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-487894880520368692504923953430757750000000000)
      constant := (20163780723028911455373081738274693516931730907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree166.table
  base := (18889026767908521941236232277718923645499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-2201662129235532625445064195020894250000000000)
      constant := (91226927738435098170540796381841415619886501638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320886727616826281817/50000000000000000000)
  centralHi := (128354691046730512727/20000000000000000000)
  directionLo := (321857642778514959969/50000000000000000000)
  directionHi := (643715285557029919939/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree167.table
  base := (76867385806473639561243939801639687395781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-490834832784533299390511070678878375000000000)
      constant := (20411262772640054408530084845111616087261590929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree167.table
  base := (76867385806457902909602089312530834582873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (7113204)
      previous := (3556602)
      next := (3556602)
      square := (27532854995542225261737079263660000000000000)
      linear := (-4429857746521966875621531799546952250000000000)
      constant := (184693036316882225445589101025428633865031018513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321857642778514959969/50000000000000000000)
  centralHi := (643715285557029919939/100000000000000000000)
  directionLo := (322825637874765181329/50000000000000000000)
  directionHi := (645651275749530362659/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree168.table
  base := (78189437895917875091443867484649231575211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3059206110615802806859675473740000000000000)
      linear := (-493774785048697906276098187926999000000000000)
      constant := (20660258862327963884172999448767822557391160299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree168.table
  base := (156378875791808658891466872320888636253451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-990309163238415222300652268678248000000000000)
      constant := (41543536589561450528175772908604297678508720459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell042.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322825637874765181329/50000000000000000000)
  centralHi := (645651275749530362659/100000000000000000000)
  directionLo := (647581478189597093179/100000000000000000000)
  directionHi := (32379073909479854659/5000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree169.table
  base := (159044526680233312591229985330930903702971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6118412221231605613719350947480000000000000)
      linear := (-993429474625725026323370610350239250000000000)
      constant := (41821537984187755847218595667258415472550629139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree169.table
  base := (39761131670052498507406288445653731431791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (3556602)
      previous := (1778301)
      next := (1778301)
      square := (13766427497771112630868539631830000000000000)
      linear := (-2241462361311885062542169309278639875000000000)
      constant := (94606245242657124332178425243982602887234868671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell042.Kernel169
