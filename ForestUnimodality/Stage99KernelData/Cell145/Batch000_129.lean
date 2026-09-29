import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell145.Parameters
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch000_049
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch050_099
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch100_149
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree000.table
  base := (5372351592718798467650742613/100000000000000000000000000)
  polynomial :=
    { denominator := 37630000000000000000000000000000000000000000
      center := (231333)
      previous := (0)
      next := (205175)
      square := (5401321504968120367218276221200000000000000)
      linear := (-24733150454946543594925145856800000000000000)
      constant := (2021615904340083863376974445271900000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree000.table
  base := (5372351592718798467650742613/100000000000000000000000000)
  polynomial :=
    { denominator := 451560000000000000000000000000000000000000000
      center := (2776721)
      previous := (0)
      next := (2461375)
      square := (64815858059617444406619314654400000000000000)
      linear := (-296797805459358523139101750281600000000000000)
      constant := (24259390852081006360523693343262800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree001.table
  base := (160937345777875708773764631838180807701903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-114614015984529191632353418567394600000000000000)
      constant := (4612832654065147665656816972085317654230896203214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree001.table
  base := (80454670157701503529648391683066951817999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-4126307124999487203278493753784500600000000000000)
      constant := (166033994180792242923333878773097371021062123783664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49909309499817069173/100000000000000000000)
  directionHi := (24954654749908534587/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree002.table
  base := (201701243313501328619095005376697990197451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-136157186807094539717003513275650800000000000000)
      constant := (2977606021491083190619511222870008903156249529219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree002.table
  base := (50409732775193888938040409514228748629403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-4902063824168276038839667848640018800000000000000)
      constant := (107163409045140594884496279770920948951124538271408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49909309499817069173/100000000000000000000)
  centralHi := (24954654749908534587/50000000000000000000)
  directionLo := (70582422383317652007/100000000000000000000)
  directionHi := (8822802797914706501/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree003.table
  base := (66536332921132810708946624139597433472303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-157700357629659887801653607983907000000000000000)
      constant := (2083680549153857715530444780685100974868134598414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree003.table
  base := (33254889821977430753933585020276792895181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-1892606841112354958133613981165179000000000000000)
      constant := (24995928436240675139095297307048903686590587788272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70582422383317652007/100000000000000000000)
  centralHi := (8822802797914706501/12500000000000000000)
  directionLo := (86445459824363193923/100000000000000000000)
  directionHi := (21611364956090798481/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree004.table
  base := (11570729013996199350542839685419584761127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-179243528452225235886303702692163200000000000000)
      constant := (1599380799799145389628654203704118449019063603704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree004.table
  base := (92524365996636797923241928358376145645977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-6453577222505853709962016038351055200000000000000)
      constant := (57560143483765989702791575046417819064963345644068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86445459824363193923/100000000000000000000)
  centralHi := (21611364956090798481/25000000000000000000)
  directionLo := (49909309499817069173/50000000000000000000)
  directionHi := (99818618999634138347/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree005.table
  base := (33788230721641221292285324629180243499911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-200786699274790583970953797400419400000000000000)
      constant := (1346228028884187190302654393001538033839782489918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree005.table
  base := (33772423670589214658190493992447726557303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-7229333921674642545523190133206573400000000000000)
      constant := (48453095919320474379068133247383420002388303822904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49909309499817069173/50000000000000000000)
  centralHi := (99818618999634138347/100000000000000000000)
  directionLo := (111600608751666994379/100000000000000000000)
  directionHi := (5580030437583349719/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree006.table
  base := (51296278166962441993634398492095012147263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-222329870097355932055603892108675600000000000000)
      constant := (1227815902333932221349710218482840036062296967447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree006.table
  base := (10254387132386374561029760287754760822197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-2668363540281143793694788076020697200000000000000)
      constant := (14731870286286247814256970821183602252813308277580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111600608751666994379/100000000000000000000)
  centralHi := (5580030437583349719/5000000000000000000)
  directionLo := (15281542711149117489/12500000000000000000)
  directionHi := (122252341689192939913/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree007.table
  base := (20013498355016827151720536821151399865763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-243873040919921280140253986816931800000000000000)
      constant := (1191776071424779357446381288210988268371562787894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree007.table
  base := (20003848686783812602757817944570173222787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-8780847320012220216645538322917609800000000000000)
      constant := (42902607179695296206111544450160710702713577112216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15281542711149117489/12500000000000000000)
  centralHi := (122252341689192939913/100000000000000000000)
  directionLo := (132047621043469436797/100000000000000000000)
  directionHi := (66023810521734718399/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree008.table
  base := (31742668071104594269440551402124154757519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-265416211742486628224904081525188000000000000000)
      constant := (1209420755911643932368831527190010590348623060711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree008.table
  base := (6345356050869129904621114606527923419907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-9556604019181009052206712417773128000000000000000)
      constant := (43541629011033014344451887309807693392089395170940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132047621043469436797/100000000000000000000)
  centralHi := (66023810521734718399/50000000000000000000)
  directionLo := (70582422383317652007/50000000000000000000)
  directionHi := (28232968953327060803/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree009.table
  base := (12659677834279092629850109892224589366967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-286959382565051976309554176233444200000000000000)
      constant := (1264834823853545847722944353071005017783711474846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree009.table
  base := (25305780662784372807548341674304531583421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-3444120239449932629255962170876215400000000000000)
      constant := (15180001092600832152240453848471794552494947497788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70582422383317652007/50000000000000000000)
  centralHi := (28232968953327060803/20000000000000000000)
  directionLo := (149727928499451207519/100000000000000000000)
  directionHi := (935799553121570047/625000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree010.table
  base := (10060907724859831725034521296223927519213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-308502553387617324394204270941700400000000000000)
      constant := (1349023112108365545723654811781741251031613653994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree010.table
  base := (2513731277884952857356069470594742610411/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-11108117417518586723329060607484164400000000000000)
      constant := (48574105809536289329666654392524561606977224804192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149727928499451207519/100000000000000000000)
  centralHi := (935799553121570047/625000000000000000)
  directionLo := (157827094465700988127/100000000000000000000)
  directionHi := (4932096702053155879/3125000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree011.table
  base := (15781325747590111773725559955018301383679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-330045724210182672478854365649956600000000000000)
      constant := (1456764459557436637887786738720698420685828481751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree011.table
  base := (492829223946426534422373891322965444201/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-11883874116687375558890234702339682600000000000000)
      constant := (52456111371303876883979354329987946278995256924288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157827094465700988127/100000000000000000000)
  centralHi := (4932096702053155879/3125000000000000000)
  directionLo := (3310609063132271063/2000000000000000000)
  directionHi := (165530453156613553151/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree012.table
  base := (6037982540276819111988560036077996042453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-351588895032748020563504460358212800000000000000)
      constant := (1584916420516347700314823053341658242284931309114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree012.table
  base := (12066085120652633595954971009902281840993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-4219876938618721464817136265731733600000000000000)
      constant := (19024326381490936733626288454506932712249104093804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3310609063132271063/2000000000000000000)
  centralHi := (165530453156613553151/100000000000000000000)
  directionLo := (172890919648726387847/100000000000000000000)
  directionHi := (21611364956090798481/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree013.table
  base := (354634565412116629514321038819668529237/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-373132065855313368648154555066469000000000000000)
      constant := (1731498421870753032854895845298924147449434026325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree013.table
  base := (2214183854768015900048979517262784621049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-13435387515024953230012582892050719000000000000000)
      constant := (62353461842009619136827212916658411279580290808464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172890919648726387847/100000000000000000000)
  centralHi := (21611364956090798481/12500000000000000000)
  directionLo := (179950574524592431259/100000000000000000000)
  directionHi := (8997528726229621563/5000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree014.table
  base := (757250413713053198807087298850641642439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-394675236677878716732804649774725200000000000000)
      constant := (1895193290334129249798592642225041431322990497528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree014.table
  base := (6049528124540938342923193949709023594593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-14211144214193742065573756986906237200000000000000)
      constant := (68250172660391565292381858059501970972279277183812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179950574524592431259/100000000000000000000)
  centralHi := (8997528726229621563/5000000000000000000)
  directionLo := (46685884139694345667/25000000000000000000)
  directionHi := (186743536558777382669/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree015.table
  base := (896730717990774368165827683898392969553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-416218407500444064817454744482981400000000000000)
      constant := (2075074105041563482202036059938677168109129337828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree015.table
  base := (715807711554497077139505802209033571833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-4995633637787510300378310360587251800000000000000)
      constant := (24909920105687224922866827745141696478479735186620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46685884139694345667/25000000000000000000)
  centralHi := (186743536558777382669/100000000000000000000)
  directionLo := (24162240564187891559/12500000000000000000)
  directionHi := (193297924513503132473/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree016.table
  base := (702014383274449244180243006183009768421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-437761578323009412902104839191237600000000000000)
      constant := (2270452765954355079680644596389446926498984446298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree016.table
  base := (698345914841106345053010776495839976451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-15762657612531319736696105176617273600000000000000)
      constant := (81767462981030611713932165969707215174172156975768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24162240564187891559/12500000000000000000)
  centralHi := (193297924513503132473/100000000000000000000)
  directionLo := (49909309499817069173/25000000000000000000)
  directionHi := (199637237999268276693/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree017.table
  base := (-528438431679433090287805780776109614727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-459304749145574760986754933899493800000000000000)
      constant := (2480794593231160927295028062461396411692940791137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree017.table
  base := (-535261468435050337468167086877140929321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-16538414311700108572257279271472791800000000000000)
      constant := (89344037284049425804316895020943800748093913051036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49909309499817069173/25000000000000000000)
  centralHi := (199637237999268276693/100000000000000000000)
  directionLo := (102890677384694352963/50000000000000000000)
  directionHi := (205781354769388705927/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree018.table
  base := (-1120444378199459790927494235264877235737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-480847919968140109071405028607750000000000000000)
      constant := (2705668975655818697597414937859870257155422480894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree018.table
  base := (-1123613206936989998357806622003978402619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-5771390336956299135939484455442770000000000000000)
      constant := (32481327916310630862804598292970376956517558017336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102890677384694352963/50000000000000000000)
  centralHi := (205781354769388705927/100000000000000000000)
  directionLo := (105873633574976478011/50000000000000000000)
  directionHi := (211747267149952956023/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree019.table
  base := (-3758465142975110819101450750599552280343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-502391090790705457156055123316006200000000000000)
      constant := (2944719885014396128177996382176321563386007742033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree019.table
  base := (-376434363696930480745177684743111799801/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-18089927710037686243379627461183828200000000000000)
      constant := (106054486535002985899473422132928485937162522507160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105873633574976478011/50000000000000000000)
  centralHi := (211747267149952956023/100000000000000000000)
  directionLo := (217549636451597125169/100000000000000000000)
  directionHi := (21754963645159712517/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree020.table
  base := (-2551170919383570486166846495002771587927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-523934261613270805240705218024262400000000000000)
      constant := (3197647490385840075491557568386864197693110640674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree020.table
  base := (-5107786357351485754682724852309742234923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-18865684409206475078940801556039346400000000000000)
      constant := (115164752253006013714054451315020559845853894248468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217549636451597125169/100000000000000000000)
  centralHi := (21754963645159712517/10000000000000000000)
  directionLo := (111600608751666994379/50000000000000000000)
  directionHi := (223201217503333988759/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree021.table
  base := (-1258115199948348020541911787682295229181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-545477432435836153325355312732518600000000000000)
      constant := (3464196099390002283494723093320665781234516542055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree021.table
  base := (-1259122245283428617383683654306434945953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-6547147036125087971500658550298288200000000000000)
      constant := (41588525411489455932412950921551529108917979236580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111600608751666994379/50000000000000000000)
  centralHi := (223201217503333988759/100000000000000000000)
  directionLo := (2858914858323628917/1250000000000000000)
  directionHi := (228713188665890313361/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree022.table
  base := (-366934870249238008115741708606702125721/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-567020603258401501410005407440774800000000000000)
      constant := (3744145807730494423036978330719319567342627863020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree022.table
  base := (-917918456224274808645144071437873802633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-20417197807544052750063149745750382800000000000000)
      constant := (134849042115096254960799646470910554653764693606624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2858914858323628917/1250000000000000000)
  centralHi := (228713188665890313361/100000000000000000000)
  directionLo := (234095411839847189357/100000000000000000000)
  directionHi := (117047705919923594679/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree023.table
  base := (-64532335135359152104645245099646807353/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-588563774080966849494655502149031000000000000000)
      constant := (4037306404082696508180789267994347634049097899904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree023.table
  base := (-4132214020844751264190118170903219301299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-21192954506712841585624323840605901000000000000000)
      constant := (145408302505700782994653743205888535876317185313768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234095411839847189357/100000000000000000000)
  centralHi := (117047705919923594679/50000000000000000000)
  directionLo := (119678319902996839731/50000000000000000000)
  directionHi := (239356639805993679463/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree024.table
  base := (-4533282710651602430686015880730586577693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-610106944903532197579305596857287200000000000000)
      constant := (4343512710860577227374831851332729301181470979766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree024.table
  base := (-9070516789586625263681474237889281390659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-7322903735293876807061832645153806400000000000000)
      constant := (52145803765717397935339031142904155266636562463548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119678319902996839731/50000000000000000000)
  centralHi := (239356639805993679463/100000000000000000000)
  directionLo := (9780187335135435193/4000000000000000000)
  directionHi := (122252341689192939913/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree025.table
  base := (-9768135065562854259413561586614651274401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-631650115726097545663955691565543400000000000000)
      constant := (4662620887812186661454817091135010275078416466231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree025.table
  base := (-9771771282507671453307468726328864664061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-22744467905050419256746672030316937400000000000000)
      constant := (167931190597025024452647277278026469932785648492876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9780187335135435193/4000000000000000000)
  centralHi := (122252341689192939913/50000000000000000000)
  directionLo := (124773273749542672933/50000000000000000000)
  directionHi := (249546547499085345867/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree026.table
  base := (-10373712014808401753212023846551717057613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-653193286548662893748605786273799600000000000000)
      constant := (4994505416584076289142221172454279119224017183403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree026.table
  base := (-2594263719343827671378296067387708113357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-23520224604219208092307846125172455600000000000000)
      constant := (179885122166569711367713669126260662576275896064048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124773273749542672933/50000000000000000000)
  centralHi := (249546547499085345867/100000000000000000000)
  directionLo := (254488543049508987193/100000000000000000000)
  directionHi := (127244271524754493597/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree027.table
  base := (-2722760940815583875640137186052863270023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-674736457371228241833255880982055800000000000000)
      constant := (5339056591348729154493874366577914127650326744452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree027.table
  base := (-5447057069295916566633829566004715497259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-8098660434462665642623006740009324600000000000000)
      constant := (64098419023328815096370053228032682076535444557496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254488543049508987193/100000000000000000000)
  centralHi := (127244271524754493597/50000000000000000000)
  directionLo := (259336379473089581771/100000000000000000000)
  directionHi := (64834094868272395443/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree028.table
  base := (-11326910633560676079717842304267239090711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-696279628193793589917905975690312000000000000000)
      constant := (5696178401591744680719116684475222073312125909841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree028.table
  base := (-11329728385847359226566398812767482121749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-25071738002556785763430194314883492000000000000000)
      constant := (205158139440024609431749543975680900536256001039084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259336379473089581771/100000000000000000000)
  centralHi := (64834094868272395443/25000000000000000000)
  directionLo := (132047621043469436797/50000000000000000000)
  directionHi := (52819048417387774719/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree029.table
  base := (-11687253120723356702084870686608758340819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-717822799016358938002556070398568200000000000000)
      constant := (6065786728899696955090836704558884020013843361589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree029.table
  base := (-11689837065397100032988049803170261897257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-25847494701725574598991368409739010200000000000000)
      constant := (218470741548425556385118796017095804226130888768412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132047621043469436797/50000000000000000000)
  centralHi := (52819048417387774719/20000000000000000000)
  directionLo := (134384928533399328587/50000000000000000000)
  directionHi := (10750794282671946287/4000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree030.table
  base := (-5988640524054544045697211760838994626757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-739365969838924286087206165106824400000000000000)
      constant := (6447807801293366486167186152820394008590057916134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree030.table
  base := (-5989824464902063593367617688638975172703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-8874417133631454478184180834864842800000000000000)
      constant := (77410136049930894719746321359799280182625311996632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134384928533399328587/50000000000000000000)
  centralHi := (10750794282671946287/4000000000000000000)
  directionLo := (273364546425566880651/100000000000000000000)
  directionHi := (68341136606391720163/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree031.table
  base := (-12201567549702222798754996891782025471463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-760909140661489634171856259815080600000000000000)
      constant := (6842176862422675198468887587398445683161779242753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree031.table
  base := (-12203736039913595193082761293756194792637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-27399008100063152270113716599450046600000000000000)
      constant := (246434808562573148611581153087131373398566244476492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273364546425566880651/100000000000000000000)
  centralHi := (68341136606391720163/25000000000000000000)
  directionLo := (34735409350816918033/12500000000000000000)
  directionHi := (55576654961307068853/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree032.table
  base := (-12364130244311870926490315981290938266087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-782452311484054982256506354523336800000000000000)
      constant := (7248837022126308514207429766972802675983641111297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree032.table
  base := (-12366114954729700021710210080414796118789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-28174764799231941105674890694305564800000000000000)
      constant := (261081895281212225823113219520339979486866532647724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34735409350816918033/12500000000000000000)
  centralHi := (55576654961307068853/20000000000000000000)
  directionLo := (282329689533270608029/100000000000000000000)
  directionHi := (28232968953327060803/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree033.table
  base := (-6234250755772467559861005201924255414033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-803995482306620330341156449231593000000000000000)
      constant := (7667738261312060538361343390658864311276255496846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree033.table
  base := (-12470317019455462763160033799452889481869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-9650173832800243313745354929720361000000000000000)
      constant := (92056622715231506515846642718506227085030950289668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282329689533270608029/100000000000000000000)
  centralHi := (28232968953327060803/10000000000000000000)
  directionLo := (28670715506715471831/10000000000000000000)
  directionHi := (286707155067154718311/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree034.table
  base := (-12517789443438527845765044378478051415767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-825538653129185678425806543939849200000000000000)
      constant := (8098836568871418204121441588886307529162050015377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree034.table
  base := (-6259724663044889982766637888836820122741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-29726278197569518776797238884016601200000000000000)
      constant := (291697143265899124559214692499648696857035842167512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28670715506715471831/10000000000000000000)
  centralHi := (286707155067154718311/100000000000000000000)
  directionLo := (29101878279837889497/10000000000000000000)
  directionHi := (291018782798378894971/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree035.table
  base := (-3128682696874266351629866460971312965833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-847081823951751026510456638648105400000000000000)
      constant := (8542093191997208648406464661734958092007653976892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree035.table
  base := (-782265478927824044461286615369616466803/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-30502034896738307612358412978872119400000000000000)
      constant := (307662326029782284508925219056809080636924699048768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29101878279837889497/10000000000000000000)
  centralHi := (291018782798378894971/100000000000000000000)
  directionLo := (295267456920329373033/100000000000000000000)
  directionHi := (147633728460164686517/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree036.table
  base := (-12461736991968991093483613692783217974889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-868624994774316374595106733356361600000000000000)
      constant := (8997473984174699160221879867264725553111734003759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree036.table
  base := (-1246312256370033420859566719492409570139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-10425930531969032149306529024575879200000000000000)
      constant := (108021395876292450124075053621064208852353728781080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295267456920329373033/100000000000000000000)
  centralHi := (147633728460164686517/50000000000000000000)
  directionLo := (299455856998902415039/100000000000000000000)
  directionHi := (935799553121570047/312500000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree037.table
  base := (-12360934297552503523956387963979012281657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-890168165596881722679756828064617800000000000000)
      constant := (9464948837476268569151168457411995348638661279967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree037.table
  base := (-12362199402697168996347979225646913982143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-32053548295075885283480761168583155800000000000000)
      constant := (340901644619581926868701253987583851211388116961988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299455856998902415039/100000000000000000000)
  centralHi := (935799553121570047/312500000000000000)
  directionLo := (151793238869272124489/50000000000000000000)
  directionHi := (303586477738544248979/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree038.table
  base := (-6107099340917874902976407693337852358927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-911711336419447070764406922772874000000000000000)
      constant := (9944491187742228499747976399151734773001090042674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree038.table
  base := (-763459583727872507496409681221223259141/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-32829304994244674119041935263438674000000000000000)
      constant := (358173741109022657944609765191729767378967603618496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151793238869272124489/50000000000000000000)
  centralHi := (303586477738544248979/100000000000000000000)
  directionLo := (307661646359184903203/100000000000000000000)
  directionHi := (76915411589796225801/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree039.table
  base := (-751449146707378108640385374264840076309/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-933254507242012418849057017481130200000000000000)
      constant := (10436077582865290361276628196213832895183866620464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree039.table
  base := (-12024239808382849567651055445247034463079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-11201687231137820984867703119431397400000000000000)
      constant := (125293211071058524133640491934309800999297725195788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307661646359184903203/100000000000000000000)
  centralHi := (76915411589796225801/25000000000000000000)
  directionLo := (19480221120487734857/6250000000000000000)
  directionHi := (311683537927803757713/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree040.table
  base := (-589468017319082732854847608490093776307/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-954797678064577766933707112189386400000000000000)
      constant := (10939687305776465622215199164971584746032893682340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree040.table
  base := (-736895071324626384601629310692644126617/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-34380818392582251790164283453149710400000000000000)
      constant := (394018575484637635037625553202743069615501627874752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19480221120487734857/6250000000000000000)
  centralHi := (311683537927803757713/100000000000000000000)
  directionLo := (157827094465700988127/50000000000000000000)
  directionHi := (63130837786280395251/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree041.table
  base := (-2878503463455666402988093906544302395591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-976340848887143115018357206897642600000000000000)
      constant := (11455302044902094951162439572849419763365306340484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree041.table
  base := (-5757444920106836848307213678930856287383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-35156575091751040625725457548005228600000000000000)
      constant := (412589909049657335209710251115880674135977978963656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157827094465700988127/50000000000000000000)
  centralHi := (63130837786280395251/20000000000000000000)
  directionLo := (319575509331816201749/100000000000000000000)
  directionHi := (1278302037327264807/400000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree042.table
  base := (-223965810540126039039202434668153758763/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-997884019709708463103007301605898800000000000000)
      constant := (11982905605860608747412348188963722892896534452650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree042.table
  base := (-5599544468010300537072771888162430947809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-11977443930306609820428877214286915600000000000000)
      constant := (143864350410004209126495324331825421104876665126696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319575509331816201749/100000000000000000000)
  centralHi := (1278302037327264807/400000000000000000)
  directionLo := (64689858660979705249/20000000000000000000)
  directionHi := (161724646652449263123/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree043.table
  base := (-10843202333411886064678296899399948408411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1019427190532273811187657396314155000000000000000)
      constant := (12522483659021477301951618729258553206945619218541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree043.table
  base := (-2168785962665212671762722278523290636591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-36708088490088618296847805737716265000000000000000)
      constant := (451027486456079835538806905270084692465705694101780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64689858660979705249/20000000000000000000)
  centralHi := (161724646652449263123/50000000000000000000)
  directionLo := (40909653604426533047/12500000000000000000)
  directionHi := (327277228835412264377/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree044.table
  base := (-10449645173680008412600047603644021735861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1040970361354839159272307491022411200000000000000)
      constant := (13074023518280222645571560078242576836380534879491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree044.table
  base := (-10450307831966042426289709596486100958453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-37483845189257407132408979832571783200000000000000)
      constant := (470892758303781600324617226927140190853980767491948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40909653604426533047/12500000000000000000)
  centralHi := (327277228835412264377/100000000000000000000)
  directionLo := (331060906313227106301/100000000000000000000)
  directionHi := (165530453156613553151/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree045.table
  base := (-10018412583954666539852068974615052691267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1062513532177404507356957585730667400000000000000)
      constant := (13637513947030938164711753275485109018947754455877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree045.table
  base := (-5009508013534814149010214054694510585001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-12753200629475398655990051309142433800000000000000)
      constant := (163729487503568563694066877969727294088108327395944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331060906313227106301/100000000000000000000)
  centralHi := (165530453156613553151/50000000000000000000)
  directionLo := (334801826255000983137/100000000000000000000)
  directionHi := (167400913127500491569/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree046.table
  base := (-9550207763233063503113254209675533799551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1084056702999969855441607680438923600000000000000)
      constant := (14212944987856982833562308614578546506233145715881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree046.table
  base := (-1910151426835502376298870700848686995657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-39035358587594984803531328022282819600000000000000)
      constant := (511914240846107442184992263164238264643411030514060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334801826255000983137/100000000000000000000)
  centralHi := (167400913127500491569/50000000000000000000)
  directionLo := (338501406257688087591/100000000000000000000)
  directionHi := (42312675782211010949/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree047.table
  base := (-4522827069338663952348444656386997078539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1105599873822535203526257775147179800000000000000)
      constant := (14800307812924381720714736174761643458930762973818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree047.table
  base := (-2261538538077977376724247621124366654129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-39811115286763773639092502117138337800000000000000)
      constant := (533069775726214962585352598966069006403727908956656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338501406257688087591/100000000000000000000)
  centralHi := (42312675782211010949/12500000000000000000)
  directionLo := (34216098727526042479/10000000000000000000)
  directionHi := (342160987275260424791/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree048.table
  base := (-425265232681553393827813301645847186183/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1127143044645100551610907869855436000000000000000)
      constant := (15399594592461941909950803044762162113909485101460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree048.table
  base := (-8505759629776456801242492942492818601571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-13528957328644187491551225403997952000000000000000)
      constant := (184884928493547762368911917157467240087784931694012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34216098727526042479/10000000000000000000)
  centralHi := (342160987275260424791/100000000000000000000)
  directionLo := (69156367859490555139/20000000000000000000)
  directionHi := (21611364956090798481/6250000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree049.table
  base := (-396482496938159068761717340471676570339/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1148686215467665899695557964563692200000000000000)
      constant := (16010798379056475223162106220678549476013187454180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree049.table
  base := (-3965031916567486195502962549655793193387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-41362628685101351310214850306849374200000000000000)
      constant := (576669020188126061791837268471606876180536508626984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69156367859490555139/20000000000000000000)
  centralHi := (21611364956090798481/6250000000000000000)
  directionLo := (87341291624679871053/25000000000000000000)
  directionHi := (349365166498719484213/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree050.table
  base := (-3659562752887145865825473373290331314243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1170229386290231247780208059271948400000000000000)
      constant := (16633913005788699356577478195185775145048654025866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree050.table
  base := (-7319501938823657580197361091336414873727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-42138385384270140145776024401704892400000000000000)
      constant := (599112258010475555226076240974631011338220832724932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87341291624679871053/25000000000000000000)
  centralHi := (349365166498719484213/100000000000000000000)
  directionLo := (88228027979147065009/25000000000000000000)
  directionHi := (352912111916588260037/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree051.table
  base := (-667411808497310908966302777767984633093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1191772557112796595864858153980204600000000000000)
      constant := (17268932996492085552387890075481439823060001272830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree051.table
  base := (-6674460368717464363840441164250141353789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-14304714027812976327112399498853470200000000000000)
      constant := (207328100654308600397753826802002529288127507635908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88228027979147065009/25000000000000000000)
  centralHi := (352912111916588260037/100000000000000000000)
  directionLo := (71284752342187469431/20000000000000000000)
  directionHi := (89105940427734336789/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree052.table
  base := (-5994971212356483201376236417602334888191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1213315727935361943949508248688460800000000000000)
      constant := (17915853486638860834635917801060705563188619335721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree052.table
  base := (-5995282375293290476926074473309542089947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-43689898782607717816898372591415928800000000000000)
      constant := (645284977067005828234558201230061610908974542042452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71284752342187469431/20000000000000000000)
  centralHi := (89105940427734336789/25000000000000000000)
  directionLo := (179950574524592431259/50000000000000000000)
  directionHi := (359901149049184862519/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree053.table
  base := (-5281990158262698885007528495621637099293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (16424643)
      previous := (0)
      next := (14567425)
      square := (383493826852736546072497611705200000000000000)
      linear := (-23299224504866552679889780064089000000000000000)
      constant := (350465474595272535908027830164443855351270591311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree053.table
  base := (-105645459369297964289109577861539082929/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96182280000000000000000000000000000000000000000
      center := (591441573)
      previous := (0)
      next := (524272875)
      square := (13805777766698515658609914021387200000000000000)
      linear := (-838974631731632200989802767665499000000000000000)
      constant := (12622908072434081444662958110106540277223898509400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179950574524592431259/50000000000000000000)
  centralHi := (359901149049184862519/100000000000000000000)
  directionLo := (363345257656780362191/100000000000000000000)
  directionHi := (22709078603548772637/6250000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree054.table
  base := (-2267723138958852994818897874061316038023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1256402069580492640118808438104973200000000000000)
      constant := (19245379154787977774808051746787982797078367788226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree054.table
  base := (-566962908051480530728690940814109184663/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-15080470726981765162673573593708988400000000000000)
      constant := (231057205357698034848926883504961852795629092347488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363345257656780362191/100000000000000000000)
  centralHi := (22709078603548772637/6250000000000000000)
  directionLo := (183378512533789409869/50000000000000000000)
  directionHi := (366757025067578819739/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree055.table
  base := (-3755580854006192631803406883444083276671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1277945240403057988203458532813229400000000000000)
      constant := (19927977073750868992241201369721692353752264882601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree055.table
  base := (-375581432653481511671810390945508465379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-46017168880114084323581894875982483400000000000000)
      constant := (717757318883323428470192189580978280890898975941640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183378512533789409869/50000000000000000000)
  centralHi := (366757025067578819739/100000000000000000000)
  directionLo := (185068672802266273447/50000000000000000000)
  directionHi := (74027469120906509379/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree056.table
  base := (-2942608492557739373837855219017556927689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1299488411225623336288108627521485600000000000000)
      constant := (20622460871580470775663166567781451379936802980559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree056.table
  base := (-1471410279913247724207720767588296766679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-46792925579282873159143068970838001600000000000000)
      constant := (742771126973300777449327212614277381666040368969928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185068672802266273447/50000000000000000000)
  centralHi := (74027469120906509379/20000000000000000000)
  directionLo := (373487073117554765337/100000000000000000000)
  directionHi := (186743536558777382669/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree057.table
  base := (-262090015719711642566241481343071042297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1321031582048188684372758722229741800000000000000)
      constant := (21328827844644771073295307769743599211496546654456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree057.table
  base := (-524228178066327401052872240417059807371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-15856227426150553998234747688564506600000000000000)
      constant := (256070981035392053060007069727271474583186921326448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373487073117554765337/100000000000000000000)
  centralHi := (186743536558777382669/50000000000000000000)
  directionLo := (376807023502304465481/100000000000000000000)
  directionHi := (188403511751152232741/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree058.table
  base := (-243617133722838589949405840276761894909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1342574752870754032457408816937998000000000000000)
      constant := (22047075586918539000269128679312553323976641601895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree058.table
  base := (-609130265080154387694728269482164686819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-48344438977620450830265417160549038000000000000000)
      constant := (794082680751038335182738202208504148874514383906408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376807023502304465481/100000000000000000000)
  centralHi := (188403511751152232741/50000000000000000000)
  directionLo := (380097977020944903837/100000000000000000000)
  directionHi := (190048988510472451919/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree059.table
  base := (-153428185300386310721595413074034913639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1364117923693319380542058911646254200000000000000)
      constant := (22777201956683668156666864467513139787221942710018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree059.table
  base := (-76753777140715954080139978988382386357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-49120195676789239665826591255404556200000000000000)
      constant := (820380262884754656358213642810693063036398868336048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380097977020944903837/100000000000000000000)
  centralHi := (190048988510472451919/50000000000000000000)
  directionLo := (95840170110894553109/25000000000000000000)
  directionHi := (383360680443578212437/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree060.table
  base := (636833101668833820144620565950072376663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1385661094515884728626709006354510400000000000000)
      constant := (23519205047038149410984269646339042670415779736047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree060.table
  base := (318344513601188711777604120830836984421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-16631984125319342833795921783420024800000000000000)
      constant := (282368540310292392714519828111399096230660441451576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95840170110894553109/25000000000000000000)
  centralHi := (383360680443578212437/100000000000000000000)
  directionLo := (24162240564187891559/6250000000000000000)
  directionHi := (77319169805401252989/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree061.table
  base := (1612862819091236847883289363112814419993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1407204265338450076711359101062766600000000000000)
      constant := (24273083159765610749044309213230666693252737858817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree061.table
  base := (1612732077249231749129888043100125919791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-50671709075126817336948939445115592600000000000000)
      constant := (874258693819487057285698934108264248628788756168444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24162240564187891559/6250000000000000000)
  centralHi := (77319169805401252989/20000000000000000000)
  directionLo := (77960833669134234367/20000000000000000000)
  directionHi := (97451042086417792959/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree062.table
  base := (2621125954258953900354693801837523612849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1428747436161015424796009195771022800000000000000)
      constant := (25038834782171908385912749684354236544899432411481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree062.table
  base := (40953239567165943876284794187967421189/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-51447465774295606172510113539971110800000000000000)
      constant := (901839427153812971345933581254261962257022089848064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77960833669134234367/20000000000000000000)
  centralHi := (97451042086417792959/25000000000000000000)
  directionLo := (196493147994026042033/50000000000000000000)
  directionHi := (392986295988052084067/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree063.table
  base := (183076366537762973894853990025996443969/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1450290606983580772880659290479279000000000000000)
      constant := (25816458566542896674087771179077795955800001415220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree063.table
  base := (3661419723882934781052416274916866172793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-17407740824488131669357095878275543000000000000000)
      constant := (309949257490391491865842576565710446787735584984204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196493147994026042033/50000000000000000000)
  centralHi := (392986295988052084067/100000000000000000000)
  directionLo := (49517857891301038799/12500000000000000000)
  directionHi := (396142863130408310393/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree064.table
  base := (946796427214789997142457117029535640347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1471833777806146120965309385187535200000000000000)
      constant := (26605953311919154457118624205791990213294183693215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree064.table
  base := (189355381524250712322355376865968888297/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-52998979172633183843632461729682147200000000000000)
      constant := (958283686587300593114886620385582476026324877973700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49517857891301038799/12500000000000000000)
  centralHi := (396142863130408310393/100000000000000000000)
  directionLo := (79854895199707310677/20000000000000000000)
  directionHi := (199637237999268276693/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree065.table
  base := (1459603694813303990203636741437434529761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1493376948628711469049959479895791400000000000000)
      constant := (27407317947919887640463631098972681378471405158436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree065.table
  base := (729790784256764739919658598324333710803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-53774735871801972679193635824537665400000000000000)
      constant := (987147131014385800013989816776277142930071870443616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79854895199707310677/20000000000000000000)
  centralHi := (199637237999268276693/50000000000000000000)
  directionLo := (16095268689085223101/4000000000000000000)
  directionHi := (201190858613565288763/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree066.table
  base := (1743689469141619875077553896160538337007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1514920119451276817134609574604047600000000000000)
      constant := (28220551520380140031226152208848492195931992296732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree066.table
  base := (435917351887481244550318542201239117913/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-18183497523656920504918269973131061200000000000000)
      constant := (338812690481464779927077334051215376785459329401024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16095268689085223101/4000000000000000000)
  centralHi := (201190858613565288763/50000000000000000000)
  directionLo := (405465147125376243397/100000000000000000000)
  directionHi := (202732573562688121699/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree067.table
  base := (407147567529410923408458899331529705749/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1536463290273842165219259669312303800000000000000)
      constant := (29045653178593413151046760139804697028238522231620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree067.table
  base := (4071439302064498005012674464746697337809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-55326249270139550350315984014248701800000000000000)
      constant := (1046156477290130588027023543585906847326406238139912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405465147125376243397/100000000000000000000)
  centralHi := (202732573562688121699/50000000000000000000)
  directionLo := (408525304856567646723/100000000000000000000)
  directionHi := (102131326214141911681/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree068.table
  base := (4671470814842640592450384991879576934027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1558006461096407513303909764020560000000000000000)
      constant := (29882622163976327966141233253017592474068648341126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree068.table
  base := (9342875692638979049714144713935416568619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-56102005969308339185877158109104220000000000000000)
      constant := (1076302321277476256138400925405554026633093624917996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408525304856567646723/100000000000000000000)
  centralHi := (102131326214141911681/25000000000000000000)
  directionLo := (102890677384694352963/25000000000000000000)
  directionHi := (411562709538777411853/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree069.table
  base := (10574680936505017199221235188817597058039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1579549631918972861388559858728816200000000000000)
      constant := (30731457799993496573521467291089452159515735048591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree069.table
  base := (5287310590392033455694985278309643872953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-18959254222825709340479444067986579400000000000000)
      constant := (368958526360990128814901956765203466503949896217368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102890677384694352963/25000000000000000000)
  centralHi := (411562709538777411853/100000000000000000000)
  directionLo := (41457786127294423339/10000000000000000000)
  directionHi := (414577861272944233391/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree070.table
  base := (5919063327683801141305112873778503210591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1601092802741538209473209953437072400000000000000)
      constant := (31592159483199690612221319508465324048058022299758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree070.table
  base := (11838072509781719185357068171189901307053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-57653519367645916856999506298815256400000000000000)
      constant := (1137876229011589063513716015923030172484642889390452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41457786127294423339/10000000000000000000)
  centralHi := (414577861272944233391/100000000000000000000)
  directionLo := (4175712421041433791/1000000000000000000)
  directionHi := (417571242104143379101/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree071.table
  base := (1641655096205568886206798381565363352903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (12260649)
      previous := (0)
      next := (10874275)
      square := (286270039763310379462568639723600000000000000)
      linear := (-22854027796677514895181127438666600000000000000)
      constant := (457249671482718674923038217310517241013916971336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree071.table
  base := (6566595857431250081515292715840958990069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71798040000000000000000000000000000000000000000
      center := (441498639)
      previous := (0)
      next := (391358625)
      square := (10305721431479173660652471030049600000000000000)
      linear := (-822947550236826840740291273150292600000000000000)
      constant := (16469073967749020311850370380814660842691466732952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4175712421041433791/1000000000000000000)
  centralHi := (417571242104143379101/100000000000000000000)
  directionLo := (210271658460636139217/50000000000000000000)
  directionHi := (84108663384254455687/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree072.table
  base := (1807498670154856523676344027465507184107/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1644179144386668905642510142853584800000000000000)
      constant := (33349158895927516655207564812394932987181353872664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree072.table
  base := (7229972462591586419829961378400471803471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-19735010921994498176040618162842097600000000000000)
      constant := (400386543304179134540630370364944719530005219518376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210271658460636139217/50000000000000000000)
  centralHi := (84108663384254455687/20000000000000000000)
  directionLo := (105873633574976478011/25000000000000000000)
  directionHi := (84698906859981182409/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree073.table
  base := (3163668433038408340929910320550996841647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1665722315209234253727160237561841000000000000000)
      constant := (34245455716606236192754904868485778916980938791715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree073.table
  base := (15818301918831073523218094379111499537061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-59980789465152283363683028583381811000000000000000)
      constant := (1233442348212553878394966879537020570087125398839124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105873633574976478011/25000000000000000000)
  centralHi := (84698906859981182409/20000000000000000000)
  directionLo := (106606331823162219291/25000000000000000000)
  directionHi := (85285065458529775433/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree074.table
  base := (17208272173245179453997272356624367130889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1687265486031799601811810332270097200000000000000)
      constant := (35153616754867673543448594003310514008091433360241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree074.table
  base := (688329429069978938323018784030259817313/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-60756546164321072199244202678237329200000000000000)
      constant := (1266152392862319428668996092569187358189355085307300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106606331823162219291/25000000000000000000)
  centralHi := (85285065458529775433/20000000000000000000)
  directionLo := (42933611417092697877/10000000000000000000)
  directionHi := (429336114170926978771/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree075.table
  base := (18629755280887452249805694869982442959183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1708808656854364949896460426978353400000000000000)
      constant := (36073641669387881930224104714623311294334891381927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree075.table
  base := (18629722280120210834948786046967633671569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-20510767621163287011601792257697615800000000000000)
      constant := (433096583864122291196794022227934782470084090421932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42933611417092697877/10000000000000000000)
  centralHi := (429336114170926978771/100000000000000000000)
  directionLo := (432227299121815969619/100000000000000000000)
  directionHi := (21611364956090798481/5000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree076.table
  base := (2008276997304963705292855503876571391143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1730351827676930297981110521686609600000000000000)
      constant := (37005530155509845108148432286991998060391499831670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree076.table
  base := (5020685024090802179840029081843980663929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-62308059562658649870366550867948365600000000000000)
      constant := (1332854413451605493123817264250646797588091225536144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432227299121815969619/100000000000000000000)
  centralHi := (21611364956090798481/5000000000000000000)
  directionLo := (435099272903194250339/100000000000000000000)
  directionHi := (21754963645159712517/5000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree077.table
  base := (21567297044150062370417582854451168860213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1751894998499495646065760616394865800000000000000)
      constant := (37949281941279280865578946908838257028308153455997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree077.table
  base := (2156726999946273267800380665270389700991/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-63083816261827438705927724962803883800000000000000)
      constant := (1366846368664752839604851502962494974009031129892440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435099272903194250339/100000000000000000000)
  centralHi := (21754963645159712517/5000000000000000000)
  directionLo := (109488103365056526571/25000000000000000000)
  directionHi := (87590482692045221257/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree078.table
  base := (23083319348686873240639692938951461902321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1773438169322060994150410711103122000000000000000)
      constant := (38904896783912985346445435575216942483333926852249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree078.table
  base := (11541647435408125074561285043815628072897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-21286524320332075847162966352553134000000000000000)
      constant := (467088536168441978818998427499955428585480780150232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109488103365056526571/25000000000000000000)
  centralHi := (87590482692045221257/20000000000000000000)
  directionLo := (17631483460237161433/4000000000000000000)
  directionHi := (220393543252964517913/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree079.table
  base := (12315410789500040107455950895530622859283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1794981340144626342235060805811378200000000000000)
      constant := (39872374466651906105616330412326775003725420997654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree079.table
  base := (6157699856807819706712749445277362631273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-64635329660165016377050073152514920200000000000000)
      constant := (1436112125182471600956948303161702774438317892579728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17631483460237161433/4000000000000000000)
  centralHi := (220393543252964517913/50000000000000000000)
  directionLo := (22180182303417497917/5000000000000000000)
  directionHi := (443603646068349958341/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree080.table
  base := (26209790067206832508882907162073589338909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1816524510967191690319710900519634400000000000000)
      constant := (40851714795956512103783434424955984415475549715621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree080.table
  base := (26209770023075430063163428908114001054509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-65411086359333805212611247247370438400000000000000)
      constant := (1471385911740109246640040469497719502143128923472756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22180182303417497917/5000000000000000000)
  centralHi := (443603646068349958341/100000000000000000000)
  directionLo := (111600608751666994379/25000000000000000000)
  directionHi := (446402435006667977517/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree081.table
  base := (13910106304324766431747760703582225210123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1838067681789757038404360995227890600000000000000)
      constant := (41842917599006789176624561055389150303742804381574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree081.table
  base := (13910097236960449143326415804052448141787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-22062281019500864682724140447408652200000000000000)
      constant := (502362320655676941759807412168768584369484557168072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111600608751666994379/25000000000000000000)
  centralHi := (446402435006667977517/100000000000000000000)
  directionLo := (449183785498353622559/100000000000000000000)
  directionHi := (2807398659364710141/625000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree082.table
  base := (29462078304494005202500826761389696070269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1859610852612322386489011089936146800000000000000)
      constant := (42845982721473403487924268742007561471213644915461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree082.table
  base := (29462061899322117040594665091965801643689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-66962599757671382883733595437081474800000000000000)
      constant := (1543215270316754208287287379562695423640824104843876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449183785498353622559/100000000000000000000)
  centralHi := (2807398659364710141/625000000000000000)
  directionLo := (56493502437418008857/12500000000000000000)
  directionHi := (451948019499344070857/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree083.table
  base := (7783844355344623689417928302726195145669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1881154023434887734573661184644403000000000000000)
      constant := (43860910025530307652027905776633586810958610632244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree083.table
  base := (15567681291314377509517865634131665201671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-67738356456840171719294769531936993000000000000000)
      constant := (1579770831836060606676497530988542242239259791852728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56493502437418008857/12500000000000000000)
  centralHi := (451948019499344070857/100000000000000000000)
  directionLo := (14209232786844968091/3125000000000000000)
  directionHi := (454695449179038978913/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree084.table
  base := (16420050633123912499408531182613694648929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1902697194257453082658311279352659200000000000000)
      constant := (44887699388082371242943132320558988755886460618002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree084.table
  base := (8210021961492415535470854109580307266959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-22838037718669653518285314542264170400000000000000)
      constant := (538917880700421875604715864247115753058659242691408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14209232786844968091/3125000000000000000)
  centralHi := (454695449179038978913/100000000000000000000)
  directionLo := (457426377331780626721/100000000000000000000)
  directionHi := (228713188665890313361/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree085.table
  base := (8644060518678517667989005213418847569349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1924240365080018430742961374060915400000000000000)
      constant := (45926350699184549057514211567290688672468884239924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree085.table
  base := (17288114969375155059129758018153503636877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-69289869855177749390417117721648029400000000000000)
      constant := (1654163697161379047341569369558635125638451092559336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457426377331780626721/100000000000000000000)
  centralHi := (228713188665890313361/50000000000000000000)
  directionLo := (460141097766353706013/100000000000000000000)
  directionHi := (230070548883176853007/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree086.table
  base := (1453751716458748819345688823202853309263/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1945783535902583778827611468769171600000000000000)
      constant := (46976863860631700508687534352150605603534333636175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree086.table
  base := (9085945484547448173974695490356375666163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-70065626554346538225978291816503547600000000000000)
      constant := (1692000993487401955288574489786775054426091215262768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460141097766353706013/100000000000000000000)
  centralHi := (230070548883176853007/50000000000000000000)
  directionLo := (231419947837461501903/50000000000000000000)
  directionHi := (462839895674923003807/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree087.table
  base := (4767843447679276706646945599628064123737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1967326706725149126912261563477427800000000000000)
      constant := (48039238784700480367700615366879336876079622652424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree087.table
  base := (38142737660586274683132392309210780567961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-23613794417838442353846488637119688600000000000000)
      constant := (576755175975697627168630849552878007969820924944908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231419947837461501903/50000000000000000000)
  centralHi := (462839895674923003807/100000000000000000000)
  directionLo := (93104609596544067187/20000000000000000000)
  directionHi := (7273797624730005249/1562500000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree088.table
  base := (39973100550487333543292512113962748683249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-1988869877547714474996911658185684000000000000000)
      constant := (49113475393026768620146191167847885381059333309081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree088.table
  base := (39973091582144297334078056821079922758239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-71617139952684115897100640006214584000000000000000)
      constant := (1768957297664608246171651579944142872475489973766076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93104609596544067187/20000000000000000000)
  centralHi := (7273797624730005249/1562500000000000000)
  directionLo := (234095411839847189357/50000000000000000000)
  directionHi := (93638164735938875743/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree089.table
  base := (20917423437357667910594902082509267183251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2010413048370279823081561752893940200000000000000)
      constant := (50199573615603925285017975372844903409761976258838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree089.table
  base := (20917419384162833689167171448748002445363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-72392896651852904732661814101070102200000000000000)
      constant := (1808076300184487838153963892239045721987540240936984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234095411839847189357/50000000000000000000)
  centralHi := (93638164735938875743/20000000000000000000)
  directionLo := (470843484135247645169/100000000000000000000)
  directionHi := (47084348413524764517/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree090.table
  base := (1093199553431993383071326153393040750419/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2031956219192845171166211847602196400000000000000)
      constant := (51297533389888770966689531432864768717992794432440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree090.table
  base := (21863987405399817356912517705581961657091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-24389551117007231189407662731975206800000000000000)
      constant := (615874177746504717998837164362786595314982286601096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470843484135247645169/100000000000000000000)
  centralHi := (47084348413524764517/10000000000000000000)
  directionLo := (473481283397102964381/100000000000000000000)
  directionHi := (236740641698551482191/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree091.table
  base := (22826251196032006583911392119286462870589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2053499390015410519250861942310452600000000000000)
      constant := (52407354660003628864121862684628803822319530739082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree091.table
  base := (45652495771169337382733027831392910068307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-73944410050190482403784162290781138600000000000000)
      constant := (1887595994822026048141169382907724005749635031899788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473481283397102964381/100000000000000000000)
  centralHi := (236740641698551482191/50000000000000000000)
  directionLo := (238052234237633370307/50000000000000000000)
  directionHi := (95220893695053348123/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree092.table
  base := (47608404113371579565663915252393838039787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2075042560837975867335512037018708800000000000000)
      constant := (53529037376024039423158733482992675601202012644003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree092.table
  base := (5951049766342688430015641780829640659601/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-74720166749359271239345336385636656800000000000000)
      constant := (1927996683138313032590486243873365688221375830179872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238052234237633370307/50000000000000000000)
  centralHi := (95220893695053348123/20000000000000000000)
  directionLo := (19148531184479494357/4000000000000000000)
  directionHi := (239356639805993679463/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree093.table
  base := (49595684151020415081859529401635307285413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2096585731660541215420162131726965000000000000000)
      constant := (54662581493342892867846099952176857302528379314797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree093.table
  base := (24797839372843232143746099863268321070431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-25165307816176020024968836826830725000000000000000)
      constant := (656274865528585787434263095946095320255135532708136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19148531184479494357/4000000000000000000)
  centralHi := (239356639805993679463/50000000000000000000)
  directionLo := (120326987634635949299/25000000000000000000)
  directionHi := (481307950538543797197/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree094.table
  base := (403237028830094080093754783487181815851/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2118128902483106563504812226435221200000000000000)
      constant := (55807986972102733463105238963154792392310660968832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree094.table
  base := (51614334807006601029205896536811136130853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-76271680147696848910467684575347693200000000000000)
      constant := (2010079733732427327245522665453912149788015845389652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120326987634635949299/25000000000000000000)
  centralHi := (481307950538543797197/100000000000000000000)
  directionLo := (241944354359820645033/50000000000000000000)
  directionHi := (483888708719641290067/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree095.table
  base := (53664368215935848006305344157286889957709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2139672073305671911589462321143477400000000000000)
      constant := (56965253776688886670794431155149154818285562292821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree095.table
  base := (10732872760958978355995058447495546977783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-77047436846865637746028858670203211400000000000000)
      constant := (2051762093298857451629054984889605621420262374558860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241944354359820645033/50000000000000000000)
  centralHi := (483888708719641290067/100000000000000000000)
  directionLo := (121613943896534327213/25000000000000000000)
  directionHi := (486455775586137308853/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree096.table
  base := (55745767480606167963595817254704001603559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2161215244128237259674112415851733600000000000000)
      constant := (58134381875276858861578916935215980707682666441471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree096.table
  base := (13936440874080323974417754043010432009323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-25941064515344808860530010921686243200000000000000)
      constant := (697957224713926675055362370481473519328721116268176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121613943896534327213/25000000000000000000)
  centralHi := (486455775586137308853/100000000000000000000)
  directionLo := (9780187335135435193/2000000000000000000)
  directionHi := (489009366756771759651/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree097.table
  base := (57858535475919737444741950507562886659911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2182758414950802607758762510559989800000000000000)
      constant := (59315371239428169997590483582405533328232185284959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree097.table
  base := (14464632969383772436062036951834488898539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-78598950245203215417151206859914247800000000000000)
      constant := (2136408475239597958330286652562074163756548797405104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9780187335135435193/2000000000000000000)
  centralHi := (489009366756771759651/100000000000000000000)
  directionLo := (491549692249529786751/100000000000000000000)
  directionHi := (3840231970699451459/781250000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree098.table
  base := (12000534081433160560985274297349035884753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2204301585773367955843412605268246000000000000000)
      constant := (60508221843729412501101151128985556100575835016285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree098.table
  base := (60002667157615809304392749303351472587683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-79374706944372004252712380954769766000000000000000)
      constant := (2179372495679411716033504106119242601731656509543372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491549692249529786751/100000000000000000000)
  centralHi := (3840231970699451459/781250000000000000)
  directionLo := (494076956683223564051/100000000000000000000)
  directionHi := (123519239170805891013/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree099.table
  base := (248712682682003933112415549836970441577/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2225844756595933303928062699976502200000000000000)
      constant := (61712933665469893050932370184219080050183736628250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree099.table
  base := (31089083868122625235137829707563978771271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-26716821214513597696091185016541761400000000000000)
      constant := (740921244881811118071259562282360314231376632915176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494076956683223564051/100000000000000000000)
  centralHi := (123519239170805891013/25000000000000000000)
  directionLo := (124147839867460164863/25000000000000000000)
  directionHi := (496591359469840659453/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree100.table
  base := (32192517416308210608718993726823864448967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2247387927418498652012712794684758400000000000000)
      constant := (62929506684353715993607993437380621507660929190846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree100.table
  base := (64385032183308391065084627579476018154797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-80926220342709581923834729144480802400000000000000)
      constant := (2266582191408638738346463658172764316046683772504948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124147839867460164863/25000000000000000000)
  centralHi := (496591359469840659453/100000000000000000000)
  directionLo := (124773273749542672933/25000000000000000000)
  directionHi := (499093094998170691733/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree101.table
  base := (33311630806288169571610124044300816631967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2268931098241064000097362889393014600000000000000)
      constant := (64157940882242614241868955542666586975693327044846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree101.table
  base := (66623259220762651264947971040379394721307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-81701977041878370759395903239336320600000000000000)
      constant := (2310827865317525107329486542659267985640120940751788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124773273749542672933/25000000000000000000)
  centralHi := (499093094998170691733/100000000000000000000)
  directionLo := (100316470561837763471/20000000000000000000)
  directionHi := (125395588202297204339/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree102.table
  base := (215290155829985196092156687538731289731/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2290474269063629348182012984101270800000000000000)
      constant := (65398236242926232010797697697127298014617255852480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree102.table
  base := (68892847706443024172956934002490002391079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-27492577913682386531652359111397279600000000000000)
      constant := (785166918596618492771725724053161684281016992788212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100316470561837763471/20000000000000000000)
  centralHi := (125395588202297204339/25000000000000000000)
  directionLo := (504059317763643860849/100000000000000000000)
  directionHi := (10081186355272877217/2000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree103.table
  base := (71193798568546249268617804506453573384443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2312017439886194696266663078809527000000000000000)
      constant := (66650392751916918882351253371861661664777614850867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree103.table
  base := (71193796619595665019378885298168618142883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-83253490440215948430518251429047357000000000000000)
      constant := (2400600862305284161127325061556071723411138819380172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504059317763643860849/100000000000000000000)
  centralHi := (10081186355272877217/2000000000000000000)
  directionLo := (506524170202270432377/100000000000000000000)
  directionHi := (253262085101135216189/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree104.table
  base := (1838152670175370427635223092280816670587/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2333560610708760044351313173517783200000000000000)
      constant := (67914410396266411261094281437855561580541169968120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree104.table
  base := (73526105047954862399845024066381872228279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-84029247139384737266079425523902875200000000000000)
      constant := (2446128184398769036495850986742323188254398139889436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506524170202270432377/100000000000000000000)
  centralHi := (253262085101135216189/50000000000000000000)
  directionLo := (254488543049508987193/50000000000000000000)
  directionHi := (508977086099017974387/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree105.table
  base := (37944886881866602262494162824520876947141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2355103781531325392435963268226039400000000000000)
      constant := (69190289164402059522609216266850459798199441253658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree105.table
  base := (75889772176198227061176768963134930130351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-28268334612851175367213533206252797800000000000000)
      constant := (830694240551562134284546139251278581221637546271828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254488543049508987193/50000000000000000000)
  centralHi := (508977086099017974387/100000000000000000000)
  directionLo := (127854559301916294257/25000000000000000000)
  directionHi := (511418237207665177029/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree106.table
  base := (15656959741649471630489804877991483146551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (16424643)
      previous := (0)
      next := (14567425)
      square := (383493826852736546072497611705200000000000000)
      linear := (-44842395327431900764539874772345200000000000000)
      constant := (1329774132943028506120233105244309592633567351615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree106.table
  base := (78284797275632688600922331944094240471963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96182280000000000000000000000000000000000000000
      center := (591441573)
      previous := (0)
      next := (524272875)
      square := (13805777766698515658609914021387200000000000000)
      linear := (-1614731330900421036550976862521017200000000000000)
      constant := (47895556107576853721956475520763235033346167741564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127854559301916294257/25000000000000000000)
  centralHi := (511418237207665177029/100000000000000000000)
  directionLo := (513847791202165446103/100000000000000000000)
  directionHi := (64230973900270680763/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree107.table
  base := (80711180987684902300462631090987624428239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2398190123176456088605263457642551800000000000000)
      constant := (71777630031756981991219635226918129213812392612391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree107.table
  base := (807111796949797241130863458772222577029/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-86356517236891103772762947808469429800000000000000)
      constant := (2585273440207429867510921782857129237025596168443600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513847791202165446103/100000000000000000000)
  centralHi := (64230973900270680763/12500000000000000000)
  directionLo := (51626591181104795773/10000000000000000000)
  directionHi := (516265911811047957731/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree108.table
  base := (4158446000925323883196871708975033397117/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2419733293999021436689913552350808000000000000000)
      constant := (73089092113468457077239237017391901393676416655460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree108.table
  base := (2599028714129448910839888356060721518633/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-29044091312019964202774707301108316000000000000000)
      constant := (877503206958507657159964059519014474230859492727168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51626591181104795773/10000000000000000000)
  centralHi := (516265911811047957731/100000000000000000000)
  directionLo := (518672758946179163543/100000000000000000000)
  directionHi := (64834094868272395443/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree109.table
  base := (85658015279135449448634670965701719898129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2441276464821586784774563647059064200000000000000)
      constant := (74412415283729322787293458843331335632348169423801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree109.table
  base := (21414503556712281743655190344780428702963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-87908030635228681443885295998180466200000000000000)
      constant := (2680173015440635801784113322071779626337752590827568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518672758946179163543/100000000000000000000)
  centralHi := (64834094868272395443/12500000000000000000)
  directionLo := (104213697765234260567/20000000000000000000)
  directionHi := (130267122206542825709/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree110.table
  base := (11022308287921529581669977681956208755873/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2462819635644152132859213741767320400000000000000)
      constant := (75747599535938114266676197099748346832659531380296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree110.table
  base := (17635693070816248620916458539208343306893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-88683787334397470279446470093035984400000000000000)
      constant := (2728263623665717562842581996446601834013412274085060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104213697765234260567/20000000000000000000)
  centralHi := (130267122206542825709/25000000000000000000)
  directionLo := (523453254094707427509/100000000000000000000)
  directionHi := (52345325409470742751/10000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree111.table
  base := (11341284084313694227462065900025719278461/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2484362806466717480943863836475576600000000000000)
      constant := (77094644864194185929765033678638552189636526559272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree111.table
  base := (22682567954549903986052663170131736096311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-29819848011188753038335881395963834200000000000000)
      constant := (925593815112963179839416657558272219654833873754832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523453254094707427509/100000000000000000000)
  centralHi := (52345325409470742751/10000000000000000000)
  directionLo := (105165440786807311051/20000000000000000000)
  directionHi := (65728400491754569407/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree112.table
  base := (23328358505018453915858455680982350327927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2505905977289282829028513931183832800000000000000)
      constant := (78453551263223248860899628277216547866642606958652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree112.table
  base := (11664179155962105374282892038942847315521/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-90235300732735047950568818282747020800000000000000)
      constant := (2825726480270769858062066484052284145406744420718112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105165440786807311051/20000000000000000000)
  centralHi := (65728400491754569407/12500000000000000000)
  directionLo := (528190484173877747189/100000000000000000000)
  directionHi := (52819048417387774719/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree113.table
  base := (19185590001425190147028375623114990224177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2527449148111848177113164025892089000000000000000)
      constant := (79824318728310829541652979550297840315038471029565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree113.table
  base := (4796397465525383198950900514257731535987/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-91011057431903836786129992377602539000000000000000)
      constant := (2875098728292082911110836102318965176505217961298160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528190484173877747189/100000000000000000000)
  centralHi := (52819048417387774719/10000000000000000000)
  directionLo := (106108647479191615463/20000000000000000000)
  directionHi := (132635809348989519329/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree114.table
  base := (3942952813522480276904238857645153352909/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2548992318934413525197814120600345200000000000000)
      constant := (81206947255242805715048220071008790537702702040525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree114.table
  base := (98573819709818302115278933757721111966647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-30595604710357541873897055490819352400000000000000)
      constant := (974966063083841033998846237266622475028787726600116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106108647479191615463/20000000000000000000)
  centralHi := (132635809348989519329/25000000000000000000)
  directionLo := (532885603034396548159/100000000000000000000)
  directionHi := (1665267509482489213/312500000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree115.table
  base := (101251044746860302100918071418215863577451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2570535489756978873282464215308601400000000000000)
      constant := (82601436840252265404532373006933679181737650749219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree115.table
  base := (25312761045080383779707116026071899251767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-92562570830241414457252340567313575400000000000000)
      constant := (2975124863013845806958431251763573091154813174681712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532885603034396548159/100000000000000000000)
  centralHi := (1665267509482489213/312500000000000000)
  directionLo := (535217717472133941653/100000000000000000000)
  directionHi := (267608858736066970827/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree116.table
  base := (12994952874465945039231771396267649573287/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2592078660579544221367114310016857600000000000000)
      constant := (84007787479972015635501669818841345097524174444024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree116.table
  base := (1624369101326093925527894781363873963159/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-93338327529410203292813514662169093600000000000000)
      constant := (3025778749458161349160947569936555580893223916758784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535217717472133941653/100000000000000000000)
  centralHi := (267608858736066970827/50000000000000000000)
  directionLo := (134384928533399328587/25000000000000000000)
  directionHi := (537539714133597314349/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree117.table
  base := (106699554872101551271850086768518579611537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2613621831402109569451764404725113800000000000000)
      constant := (85425999171392139304038962725958755041939318269753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree117.table
  base := (1667180537679459316057087339810136333869/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-31371361409526330709458229585674870600000000000000)
      constant := (1025619949492136787756515054145993567357930356245248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134384928533399328587/25000000000000000000)
  centralHi := (537539714133597314349/100000000000000000000)
  directionLo := (539851723573777293777/100000000000000000000)
  directionHi := (269925861786888646889/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree118.table
  base := (437883360743889137574860258303473850887/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2635165002224674917536414499433370000000000000000)
      constant := (86856071911822062831826182435541833853910179975750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree118.table
  base := (54735419885342732292175410896828499126089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-94889840927747780963935862851880130000000000000000)
      constant := (3128368159972001237195285716346995862513207623530952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539851723573777293777/100000000000000000000)
  centralHi := (269925861786888646889/50000000000000000000)
  directionLo := (271076936781943227807/50000000000000000000)
  directionHi := (108430774712777291123/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree119.table
  base := (112273478767487856677923292825613312752307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2656708173047240265621064594141626200000000000000)
      constant := (88298005698856654567390116195113655112222522259883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree119.table
  base := (112273478393095290575634972342554403650259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-95665597626916569799497036946735648200000000000000)
      constant := (3180303683858592378321892464317786866074497836015756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271076936781943227807/50000000000000000000)
  centralHi := (108430774712777291123/20000000000000000000)
  directionLo := (544446289173757810591/100000000000000000000)
  directionHi := (17013946536679931581/3125000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree120.table
  base := (14388433808101833573312293402347926532979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2678251343869805613705714688849882400000000000000)
      constant := (89751800530345925081394695918585101092052533707608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree120.table
  base := (115107470127312304673546062233794463269861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-32147118108695119545019403680530388800000000000000)
      constant := (1077555473353001297224519839754952791333986292398108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544446289173757810591/100000000000000000000)
  centralHi := (17013946536679931581/3125000000000000000)
  directionLo := (546729092851133761303/100000000000000000000)
  directionHi := (68341136606391720163/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree121.table
  base := (117972815142224950423500927146098311479871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2699794514692370961790364783558138600000000000000)
      constant := (91217456404367946216952342495586957656169613458199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree121.table
  base := (117972814837998204403652292818626915117467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-97217111025254147470619385136446684600000000000000)
      constant := (3285456368504244900782688273065960473745181552589228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546729092851133761303/100000000000000000000)
  centralHi := (68341136606391720163/12500000000000000000)
  directionLo := (109800480899597552181/20000000000000000000)
  directionHi := (274501202248993880453/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree122.table
  base := (7554344542399214057209438737984243151977/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2721337685514936309875014878266394800000000000000)
      constant := (92694973319204646582883303709851750337905392065808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree122.table
  base := (604347562020867938582595898464103267363/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-97992867724422936306180559231302202800000000000000)
      constant := (3338673529132644209621876934191789201510048303298400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109800480899597552181/20000000000000000000)
  centralHi := (274501202248993880453/50000000000000000000)
  directionLo := (275633170772006640207/50000000000000000000)
  directionHi := (110253268308802656083/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree123.table
  base := (61898781482419753443841495630074696731709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2742880856337501657959664972974651000000000000000)
      constant := (94184351273320177642941667716946210851689494197642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree123.table
  base := (123797562717693748273189194329604357697921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-32922874807863908380580577775385907000000000000000)
      constant := (1130772633963024438245128382227644684003918147703788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275633170772006640207/50000000000000000000)
  centralHi := (110253268308802656083/20000000000000000000)
  directionLo := (553521019017407533843/100000000000000000000)
  directionHi := (138380254754351883461/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree124.table
  base := (3961155184519429410011480775699432021887/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2764424027160067006044315067682907200000000000000)
      constant := (95685590265341577125062469208390318820285811804896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree124.table
  base := (12675696568188636870402362726467463468847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-99544381122760513977302907421013239200000000000000)
      constant := (3446389486724251947466487005120963346759271911851480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553521019017407533843/100000000000000000000)
  centralHi := (138380254754351883461/25000000000000000000)
  directionLo := (555766549613070688529/100000000000000000000)
  directionHi := (55576654961307068853/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree125.table
  base := (6487386070552861706132404214351478598679/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2785967197982632354128965162391163400000000000000)
      constant := (97198690294041485569021601640903430122143556335020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree125.table
  base := (129747721210333899352889615984899085072579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-100320137821929302812864081515868757400000000000000)
      constant := (3500888283594127371938100113598847183951381452610636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555766549613070688529/100000000000000000000)
  centralHi := (55576654961307068853/10000000000000000000)
  directionLo := (111600608751666994379/20000000000000000000)
  directionHi := (69750380469791871487/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree126.table
  base := (132769829406660671002119547644644834774981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2807510368805197702213615257099419600000000000000)
      constant := (98723651358322697820924385723095164305390807931789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree126.table
  base := (132769829225785242530929780836448150799307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-33698631507032697216141751870241425200000000000000)
      constant := (1185271430819773199532224731751983864725668066434596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111600608751666994379/20000000000000000000)
  centralHi := (69750380469791871487/12500000000000000000)
  directionLo := (280115304838166074003/50000000000000000000)
  directionHi := (560230609676332148007/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree127.table
  base := (33955822455540787067902470554817323959337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2829053539627763050298265351807675800000000000000)
      constant := (100260473457204354500947778122624089360567844191812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree127.table
  base := (67911644829591499658961329805547943761831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-101871651220266880483986429705579793800000000000000)
      constant := (3611167513284625507623422126889635245200191635079608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280115304838166074003/50000000000000000000)
  centralHi := (560230609676332148007/100000000000000000000)
  directionLo := (70306169180887781523/12500000000000000000)
  directionHi := (112489870689420450437/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree128.table
  base := (138908102595640518290058499217651074539221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2850596710450328398382915446515932000000000000000)
      constant := (101809156589809599213313409562938252598506966488349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree128.table
  base := (34727025612198499596141168516540605217283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (731706221635021329906325443133521600000000000000)
      linear := (-102647407919435669319547603800435312000000000000000)
      constant := (3666947946038575622016903748971939615794417296119088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell145.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70306169180887781523/12500000000000000000)
  centralHi := (112489870689420450437/20000000000000000000)
  directionLo := (282329689533270608029/50000000000000000000)
  directionHi := (564659379066541216059/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree129.table
  base := (8876516729483390609978901674933051225801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (870506079)
      previous := (0)
      next := (772073525)
      square := (20325172823195036941842373420375600000000000000)
      linear := (-2872139881272893746467565541224188200000000000000)
      constant := (103369700755354545799252600634068816179687989125904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree129.table
  base := (35506066884858033209309020403020532134577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (243902073878340443302108481044507200000000000000)
      linear := (-34474388206201486051702925965096943400000000000000)
      constant := (1241051863564345978724917706912631273140035971048624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell145.Kernel129
