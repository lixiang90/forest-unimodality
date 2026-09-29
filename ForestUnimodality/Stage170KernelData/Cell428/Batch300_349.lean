import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell428.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch300_349
import ForestUnimodality.BinomialMassData.Q9_35.Batch300_349

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel300
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
  base := (4282938135776177318812774857368417390233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4455286126462392422287184184000000000000)
      constant := (169919730745751849253453967407368417390233) }

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
  base := (21414690678880886447608755642511998675913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1123000238799897511944581014380000000000000)
      constant := (44003061182476899833568072422083087935119737) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel301
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
  base := (1356577090315431237608763367541417430739/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22351323817589608226874542085000000000000)
      constant := (855467665801162955767234984506287678891824) }

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
  base := (339144272578857807396484959089880631959/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (26)
      previous := (9)
      next := (0)
      square := (262126148471761404035174077500000000000)
      linear := (-40241959119210388434381697182000000000000)
      constant := (1582376949137026790411790220780966630779408) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel302
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
  base := (1374824746448164021329166801030534360837/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22426217002867254342313163250000000000000)
      constant := (861356820901843788127909902608988549773392) }

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
  base := (21997195943170624228758084962460114679699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1130549471875884240380794027812000000000000)
      constant := (44611088151743726578299485998181345619305251) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel303
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
  base := (22290578167713027858204444233669916545567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22501110188144900457751784415000000000000)
      constant := (867266119025262710994855796484294916545567) }

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
  base := (5572644541928256939898671483819241444567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-283581022103469401149725133632000000000000)
      constant := (11229165477481604147130538615251842830783783) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel304
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
  base := (11292690056589952721508245181010725878757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22576003373422546573190405580000000000000)
      constant := (873195560165925519458535616362021451757514) }

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
  base := (22585380113179905356589386232401949058117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1138098704951870968817007041244000000000000)
      constant := (45223275850115604121642654321022895503847733) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel305
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
  base := (228816017741213737058438888651029592463/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4530179311740038537725805349000000000000)
      constant := (175829028863676466025818088781145591849260) }

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
  base := (2860200221765171703761883195773651720877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-285468330372466083258778386990000000000000)
      constant := (11382732493011061222892069171033317868645946) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel306
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
  base := (724351348285355380120447766322084925513/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22725789743977838804067647910000000000000)
      constant := (885114871477227082523687967894806717616416) }

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
  base := (23179243145131372097465086156771795273653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1145647938027857697253220054676000000000000)
      constant := (45839624275447441934649336299125017968408997) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel307
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
  base := (2934788027605896476558529817729520185711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22800682929255484919506269075000000000000)
      constant := (891104741637097047637748617537461161485688) }

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
  base := (2347830422084717175428264660203064390721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-574711277282925530735663280696000000000000)
      constant := (23074679380031210764834704948647150775726645) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel308
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
  base := (11889392497974445377237262401856112627183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22875576114533131034944890240000000000000)
      constant := (897114754792672343574061298713712225254366) }

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
  base := (11889392497974445351739670948061928353657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-82371226507417458977816647722000000000000)
      constant := (3318580958973464961690867545239633498475599) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel309
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
  base := (6020171366289754190902608682860718078403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22950469299810777150383511405000000000000)
      constant := (903144910938675458106363258847067872313612) }

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
  base := (24080685465159016718917504148704006981863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1156971787641837789907539574824000000000000)
      constant := (46771948271887107637576797780679696342111287) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel310
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
  base := (4876801124648387332350700308777861799653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4605072497017684653164426514000000000000)
      constant := (181839042013974155611306406231277861799653) }

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
  base := (24384005623241936622584317598844528981207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1160746404179831154125646081540000000000000)
      constant := (47084803298581671005660738366983381920079143) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel311
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
  base := (24688745465003472391328572391291466706539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23100255670366069381260753735000000000000)
      constant := (915265652181064125366992462791916466706539) }

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
  base := (4937749093000694471400149999638797458959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1164521020717824518343752588256000000000000)
      constant := (47398698505457684843107494812096705377444955) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel312
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
  base := (24994904985290423666971370041864329431829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23175148855643715496699374900000000000000)
      constant := (921356237267102299752380276521864329431829) }

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
  base := (24994904985290423636886782976666004436313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1168295637255817882561859094972000000000000)
      constant := (47713633892262642335938346215885434217379337) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel313
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
  base := (12651242089495058546419772539922397989773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23250042040921361612137996065000000000000)
      constant := (927466965322872627816853122930469795979546) }

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
  base := (253024841789901170664739272433962636661/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-293017563448452811694991400422000000000000)
      constant := (12007402364686505621940159150774304229909725) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel314
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
  base := (5122296608205992326858968408591298035713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4664987045239801545515323446000000000000)
      constant := (186719567268660503705154549311091298035713) }

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
  base := (25611483041029961611188671386480996758727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1175844870331804610998072108404000000000000)
      constant := (48346625204659268337880263914548768841177623) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel315
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
  base := (1296095078318850516744916094402319955139/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4679965682295330768603047679000000000000)
      constant := (187949770064671804984540041670734279820556) }

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
  base := (5184380313275402062929765775387409517127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-168517069552828282173739802160000000000000)
      constant := (6952097304250823640776357287188559333099445) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel316
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
  base := (26233739750037528171906920239247266778071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23474721596754299958453859560000000000000)
      constant := (945920007258048411984892443949247266778071) }

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
  base := (3279217468754691019270135276592302546441/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-295848525851947834858571280459000000000000)
      constant := (12245944308447705228577843833202845649551218) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel317
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
  base := (26546997587056565945575617137105352861467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23549614782031946073892480725000000000000)
      constant := (952111307142415730512604433382730352861467) }

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
  base := (26546997587056565930024017004195618765087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1187168719945784703652391628552000000000000)
      constant := (49303913516521642113725517576928385319489263) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel318
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
  base := (26861675072517540099685729779453286541743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23624507967309592189331101890000000000000)
      constant := (958322749971544396949617493851953286541743) }

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
  base := (13430837536258770043028586235374817508073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-595471668241889033935249067634000000000000)
      constant := (24812544988853658244712042582211766057895577) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel319
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
  base := (1358888610077090918638928806995504557139/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4739880230517447660953944611000000000000)
      constant := (192910867148111155806894588666107018228556) }

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
  base := (27177772201541818360835369369671065456591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1194717953021771432088604641984000000000000)
      constant := (49947306617108791060597244312403082207372959) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel320
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
  base := (27495288969288311181569808276928894808837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23774294337864884420208344220000000000000)
      constant := (970806064444608787183886433876928894808837) }

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
  base := (27495288969288311171103625686530007304791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1198492569559764796306711148700000000000000)
      constant := (50270563434488852437665500902159970357934759) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel321
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
  base := (27814225370953068639980809685620020599627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23849187523142530535646965385000000000000)
      constant := (977077936078899471511779348986245020599627) }

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
  base := (434597271421141697356391633406993345587/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-300566796524439540131204413854000000000000)
      constant := (12648715107403026769053065991603382782940208) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel322
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
  base := (28134581401768883119146118732830315176869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23924080708420176651085586550000000000000)
      constant := (983369950638660624389286227025330315176869) }

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
  base := (14067290700884441555554392591122034881893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-86145843045410823195923154438000000000000)
      constant := (3637156971588925843030302240629054244173251) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel323
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
  base := (28456357057004897255617503700011568719151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-23998973893697822766524207715000000000000)
      constant := (989682108119161388452958836275636568719151) }

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
  base := (28456357057004897248574330424036364732053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1209816419173744888961030668848000000000000)
      constant := (51246574952155604605493408706780581871870597) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel324
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
  base := (7194888082991554329206067217187919099389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24073867078975468881962828880000000000000)
      constant := (996014408515706869970226481018751676397556) }

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
  base := (28779552331966217310652336658259309941897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1213591035711738253179137175564000000000000)
      constant := (51573992479113985692524681163681906187152953) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel325
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
  base := (5820833444398706366925585648796193734577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4829752052850622999480290009000000000000)
      constant := (200473370364727551494590135051921193734577) }

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
  base := (29104167221993531829219509113479599643099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1217365652249731617397243682280000000000000)
      constant := (51902450182891798801580007295710500382511851) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel326
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
  base := (5886040344492547083911513492516801716207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4844730689906152222568014242000000000000)
      constant := (201747887607665989114332100927016801716207) }

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
  base := (29430201722462735414818248077225144484887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1221140268787724981615350188996000000000000)
      constant := (52231948063262462768575964716955232079759463) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel327
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
  base := (14878827914392278835018839518308174971279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24298546634808407228278692375000000000000)
      constant := (1015132167155194163864780461657241349942558) }

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
  base := (29757655828784557665884715839831443753903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1224914885325718345833456695712000000000000)
      constant := (52562486120001103343835925379642540743941247) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel328
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
  base := (30086529536404197092549446526575971098997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24373439820086053343717313540000000000000)
      constant := (1021545039169675610858791729886575971098997) }

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
  base := (30086529536404197088910323974891710224949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1228689501863711710051563202428000000000000)
      constant := (52894064352884535254177968450878493801022501) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel329
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
  base := (30416822840800959950349571670863558792543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24448333005363699459155934705000000000000)
      constant := (1027978054077253592816951011061488558792543) }

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
  base := (6083364568160191989432147701833403156829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-176066302628815010609952815592000000000000)
      constant := (7603811823098749215214587366567769110489015) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel330
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
  base := (15374267868743951979962209837597458865083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24523226190641345574594555870000000000000)
      constant := (1034431211873441167455744670387694917730166) }

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
  base := (15374267868743951978565090638851734667113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-618119367469849219243888107930000000000000)
      constant := (26780170673100685464458285797423734998688537) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel331
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
  base := (15540834111005743377969357706279155664061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24598119375918991690033177035000000000000)
      constant := (1040904512553784792409837432738183311328122) }

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
  base := (1942604263875717922093141432847023462673/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-310003337869422950676470680644000000000000)
      constant := (13473760026549172736380064364776316598683908) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel332
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
  base := (31416220289951219046958295899725276631747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24673012561196637805471798200000000000000)
      constant := (1047397956113863978387795135129725276631747) }

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
  base := (15708110144975609522406427649344189199791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-621893984007842583461994614646000000000000)
      constant := (27115389520730300290516595439600265270789759) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel333
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
  base := (31752191936919322385716878035878964155899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24747905746474283920910419365000000000000)
      constant := (1053911542549290946942351494461503964155899) }

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
  base := (6350438387383864476767392858648149333309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1247562584553678531142095736008000000000000)
      constant := (54567558151778098691539583144043596586660705) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel334
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
  base := (501399736852506116861878263619283287797/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24822798931751930036349040530000000000000)
      constant := (1060445271855710292780452257784134130419008) }

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
  base := (32089583158560391477512972257937924075233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1251337201091671895360202242724000000000000)
      constant := (54905377436935770417680002988722158279686417) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel335
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
  base := (32428393950551060964915087169805297588449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-24897692117029576151787661695000000000000)
      constant := (1066999144028798650539724223860430297588449) }

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
  base := (16214196975275530481735870156242991556527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-627555908814832629789154374720000000000000)
      constant := (27622118448360885428349181304050906586269823) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel336
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
  base := (3276862430859967658224906748282952479123/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4994517060461444453445256572000000000000)
      constant := (214714631812852873191886989448565904958246) }

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
  base := (16384312154299838290492191605326575385937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-89920459583404187414029661154000000000000)
      constant := (3970295466494700639272781901794086027701559) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel337
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
  base := (8277568557111492666731553614094638166581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25047478487584868382664904025000000000000)
      constant := (1080167316957847171375348492577003552666324) }

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
  base := (8277568557111492666454521422076560867277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-315665262676412997003630440718000000000000)
      constant := (13981269084834782895373586772956451482496573) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel338
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
  base := (33453343705860741900714117017981782837617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25122371672862514498103525190000000000000)
      constant := (1086781617705317865469232448790481782837617) }

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
  base := (16726671852930370949871585517060920040463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-633217833621822676116314134794000000000000)
      constant := (28133528160877253943565654924686385081982687) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel339
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
  base := (33797832736645539247601182241828560193819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25197264858140160613542146355000000000000)
      constant := (1093416061302477997205075222957453560193819) }

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
  base := (16898916368322769623375221309973820210827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-635105141890819358225367388152000000000000)
      constant := (28305038238983106882982692131489317190330523) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel340
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
  base := (34143741316632350010062209626627952564783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25272158043417806728980767520000000000000)
      constant := (1100070647745159553885351614576627952564783) }

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
  base := (1707187065831617500465839997840712157743/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-318496225079908020167210320755000000000000)
      constant := (14238534201942504148954484602170974478647035) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel341
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
  base := (34491069441683291939950788651527332706609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25347051228695452844419388685000000000000)
      constant := (1106745377029224653261915213127152332706609) }

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
  base := (34491069441683291939297672868423245084873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1277759516857625444886947789736000000000000)
      constant := (57299237310963160146529888347849939009158777) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel342
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
  base := (1088744284615322166869857229533900438153/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25421944413973098959858009850000000000000)
      constant := (1113440249150565239637334530637584814020896) }

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
  base := (17419908553845154669631593077124200474367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-640767066697809404552527148226000000000000)
      constant := (28822688993672174844463585097825485823243983) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel343
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
  base := (35189984310574873091781414435565204401543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25496837599250745075296631015000000000000)
      constant := (1120155264105102783893674843836190204401543) }

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
  base := (3518998431057487309128002986903820034409/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-91807767852400869523082914512000000000000)
      constant := (4142325631193838378302217983197833701204315) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel344
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
  base := (35541571046287684551751813993670082014727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25571730784528391190735252180000000000000)
      constant := (1126890421888787987386899228793670082014727) }

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
  base := (17770785523143842275656259309711465288641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-644541683235802768770633654942000000000000)
      constant := (29170389929436453667441892235465461799143409) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel345
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
  base := (35894577310808383248960547158057635190419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25646623969806037306173873345000000000000)
      constant := (1133645722497600489646221602648682635190419) }

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
  base := (1121705540962761976517989215535926062539/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-323214495752399725439843454150000000000000)
      constant := (14672510263406215535454225859057583016515288) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel346
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
  base := (36249003100145258330609713070860476856163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25721517155083683421612494510000000000000)
      constant := (1140421165927548579818844064543360476856163) }

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
  base := (2265562693759078645642030559521860307239/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-324158149886898066494370080829000000000000)
      constant := (14760085605193501971310839530731084620218844) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel347
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
  base := (36604848410334963693570019762605717358103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25796410340361329537051115675000000000000)
      constant := (1147216752174668911801637322508230717358103) }

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
  base := (18302424205167481846637281138001944690347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-650203608042792815097793415016000000000000)
      constant := (29695841980063070303054927032035495289827003) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel348
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
  base := (36962113237442236745599326488611014945889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25871303525638975652489736840000000000000)
      constant := (1154032481235026223002359235798611014945889) }

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
  base := (18481056618721118372670232241364816728793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-652090916311789497206846668374000000000000)
      constant := (29872032835744216218698281075393276019710857) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel349
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
  base := (37320797577559620739795746117226381533331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-25946196710916621767928358005000000000000)
      constant := (1160868353104713056674107917282851381533331) }

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
  base := (1492831903102384829582757937905205309927/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1307956449161572358631799843464000000000000)
      constant := (60097487554669417998505321273951076504660575) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel349
