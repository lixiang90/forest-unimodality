import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell012.Parameters
import ForestUnimodality.BinomialMassData.Q29_85.Batch000_049
import ForestUnimodality.BinomialMassData.Q29_85.Batch050_099
import ForestUnimodality.BinomialMassData.Q29_85.Batch100_149
import ForestUnimodality.BinomialMassData.Q89_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q89_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q89_255.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree000.table
  base := (216261955041868129706372771/25000000000000000000000000)
  polynomial :=
    { denominator := 34000000000000000000000000000000000000000
      center := (56)
      previous := (29)
      next := (0)
      square := (811624267107114091834851890000000000000)
      linear := (1739123542598366337075255224000000000000)
      constant := (294116258856940656400666968560000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree000.table
  base := (216261955041868129706372771/25000000000000000000000000)
  polynomial :=
    { denominator := 102000000000000000000000000000000000000000
      center := (166)
      previous := (89)
      next := (0)
      square := (2434872801321342275504555670000000000000)
      linear := (5217370627795099011225765672000000000000)
      constant := (882348776570821969202000905680000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree001.table
  base := (29566928651599176644833982647522587466359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (100751293628648521324975284420000000000000)
      constant := (17047280483872937158718072632766055555555502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree001.table
  base := (14627490728681910226619698256035803537101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (897022151452551322822759337100000000000000)
      constant := (151795701388506423723651351767702499999998804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (30182430530369648237/100000000000000000000)
  directionHi := (15091215265184824119/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree002.table
  base := (20286415559656009211871395199947487889273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (53677086136435903998553874800000000000000)
      constant := (11656800251946330804028153878553647999999794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree002.table
  base := (39734971342130733437877516799011180315263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (463614792817352397782948427840000000000000)
      constant := (102724503821828884199517651931468079999999063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30182430530369648237/100000000000000000000)
  centralHi := (15091215265184824119/50000000000000000000)
  directionLo := (21342201300716262401/50000000000000000000)
  directionHi := (42684402601432524803/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree003.table
  base := (27893641503567651159473967485498042541827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (6602878644223286672132465180000000000000)
      constant := (7982231400180684449775346974766934294588003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree003.table
  base := (2704505034212415437113420970242007279541/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (2822)
      previous := (1513)
      next := (0)
      square := (41392837622462818683577446390000000000000)
      linear := (2013828945476898182875834572000000000000)
      constant := (4642122832053731728294315887466440622724094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21342201300716262401/50000000000000000000)
  centralHi := (42684402601432524803/100000000000000000000)
  directionLo := (5227750317451828663/10000000000000000000)
  directionHi := (52277503174518286631/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree004.table
  base := (19150278029937062032157002908092129789067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-40471328847989330654288944440000000000000)
      constant := (5461176915453851340660053258358625509040363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree004.table
  base := (9190517073198379939911925803811140030101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-403199924453045452296673390680000000000000)
      constant := (47161827202060413805811133559617550436585402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5227750317451828663/10000000000000000000)
  centralHi := (52277503174518286631/100000000000000000000)
  directionLo := (30182430530369648237/50000000000000000000)
  directionHi := (2414594442429571859/4000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree005.table
  base := (6529308589012421708826824737850681760961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-87545536340201947980710354060000000000000)
      constant := (3722525100371558673306319290847694057835458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree005.table
  base := (1549917394412659475877725190579763502359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-836607283088244377336484299940000000000000)
      constant := (31819797042909637761545846459393718957086072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30182430530369648237/50000000000000000000)
  centralHi := (2414594442429571859/4000000000000000000)
  directionLo := (16872491598017891047/25000000000000000000)
  directionHi := (67489966392071564189/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree006.table
  base := (878134705858579880251563849208643693911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-26923948766482913061426352736000000000000)
      constant := (504858563788388931065519083804196055080558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree006.table
  base := (8233364504190557158417308476754455518163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-423338213907814434125431736400000000000000)
      constant := (7117241051468807887138871240298112934247321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16872491598017891047/25000000000000000000)
  centralHi := (67489966392071564189/100000000000000000000)
  directionLo := (73931553996406291367/100000000000000000000)
  directionHi := (9241444249550786421/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree007.table
  base := (5714015160990763008799846085544512500049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-181693951324627182633553173300000000000000)
      constant := (1691793295593180550298318843956364112514161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree007.table
  base := (5265832305138730492855607799880641197827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-1703422000358642227416106118460000000000000)
      constant := (14152065750055574684979892452819547755548027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73931553996406291367/100000000000000000000)
  centralHi := (9241444249550786421/12500000000000000000)
  directionLo := (79855205146841423149/100000000000000000000)
  directionHi := (1597104102936828463/2000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree008.table
  base := (1736299216003152597342879162455541529659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-228768158816839799959974582920000000000000)
      constant := (1114043867940804844932361039547303004142902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree008.table
  base := (3108502844426099571895594358334785893971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-2136829358993841152455917027720000000000000)
      constant := (9211013334472160916050368197260778110218571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79855205146841423149/100000000000000000000)
  centralHi := (1597104102936828463/2000000000000000000)
  directionLo := (21342201300716262401/25000000000000000000)
  directionHi := (17073761040573009921/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree009.table
  base := (1799500660957236421617809909935615677239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-275842366309052417286395992540000000000000)
      constant := (716599231099687935987163634021392930722071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree009.table
  base := (1503768923874929430113194836872376752727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-856745572543013359165242645660000000000000)
      constant := (1952843195065297903186675420422350644614309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21342201300716262401/25000000000000000000)
  centralHi := (17073761040573009921/20000000000000000000)
  directionLo := (11318411448888618089/12500000000000000000)
  directionHi := (90547291591108944713/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree010.table
  base := (104274037701263315593224735282276837317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-64583314760253006922563480432000000000000)
      constant := (89872151104273486240338425384578005984613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree010.table
  base := (140039621097240684610126523471057812199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-3003644076264239002535538846240000000000000)
      constant := (3648409567569561711261372398416442739059198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11318411448888618089/12500000000000000000)
  centralHi := (90547291591108944713/100000000000000000000)
  directionLo := (47722612897885993827/50000000000000000000)
  directionHi := (19089045159154397531/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree011.table
  base := (-239476667179909681654544863857470578783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-369990781293477651939238811780000000000000)
      constant := (278469100340980837761447395508382005463426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree011.table
  base := (-338680067573514703126482717267891989129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-3437051434899437927575349755500000000000000)
      constant := (2282074257875992668137627374278425872550942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47722612897885993827/50000000000000000000)
  centralHi := (19089045159154397531/20000000000000000000)
  directionLo := (1564121833284432101/1562500000000000000)
  directionHi := (20020759466040730893/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree012.table
  base := (-320271752004492681066240328515017356181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-417064988785690269265660221400000000000000)
      constant := (180914923549633151591918577420639936254764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree012.table
  base := (-144583660151256907266443708640363797253/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (2822)
      previous := (1513)
      next := (0)
      square := (41392837622462818683577446390000000000000)
      linear := (-258030586235642456841010710984000000000000)
      constant := (103899943065207437032112957825609175563298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1564121833284432101/1562500000000000000)
  centralHi := (20020759466040730893/20000000000000000000)
  directionLo := (5227750317451828663/5000000000000000000)
  directionHi := (104555006349036573261/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree013.table
  base := (-1939505019801934304390592931137600259079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-464139196277902886592081631020000000000000)
      constant := (140955185007857097640755238439233525126169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree013.table
  base := (-2077785947913137233775043146841935744253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-4303866152169835777654971574020000000000000)
      constant := (1341298739456308403911521277226125129197947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5227750317451828663/5000000000000000000)
  centralHi := (104555006349036573261/100000000000000000000)
  directionLo := (10882430089537753603/10000000000000000000)
  directionHi := (108824300895377536031/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree014.table
  base := (-2491791148170514073141924428248189262571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-511213403770115503918503040640000000000000)
      constant := (147728172741058328735190762116273303116981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree014.table
  base := (-2609119398165832324577740134379269748749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-4737273510805034702694782483280000000000000)
      constant := (1537067945162310184010428199111519383503851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10882430089537753603/10000000000000000000)
  centralHi := (108824300895377536031/100000000000000000000)
  directionLo := (56466157072374461871/50000000000000000000)
  directionHi := (112932314144748923743/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree015.table
  base := (-1482068773540197682345193962885581616177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-558287611262328121244924450260000000000000)
      constant := (193664354255754783299681265662133825849694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree015.table
  base := (-766177653910683039604500216585369645161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-1723560289813411209244864464180000000000000)
      constant := (693703454888447501088946778391938070581652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56466157072374461871/50000000000000000000)
  centralHi := (112932314144748923743/100000000000000000000)
  directionLo := (4675842031687357623/4000000000000000000)
  directionHi := (3653001587255748143/3125000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree016.table
  base := (-3375014755174533424774493260091946934387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-605361818754540738571345859880000000000000)
      constant := (273425743884132395315797406361427335962157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree016.table
  base := (-3462018251956577266856127577101794039573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-5604088228075432552774404301800000000000000)
      constant := (2928016045120667239092411573814233703070627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4675842031687357623/4000000000000000000)
  centralHi := (3653001587255748143/3125000000000000000)
  directionLo := (120729722121478592949/100000000000000000000)
  directionHi := (2414594442429571859/2000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree017.table
  base := (-747525296970699146765075388097046623887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34000000000000000000000000000000000000000
      center := (56)
      previous := (29)
      next := (0)
      square := (811624267107114091834851890000000000000)
      linear := (-7675717955844157128209026700000000000000)
      constant := (4508193749910907799281655682750207393921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree017.table
  base := (-953370907189590516018931994015006756641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2490)
      previous := (1335)
      next := (0)
      square := (36523092019820134132568335050000000000000)
      linear := (-355146799218272439871424424180000000000000)
      constant := (237966182877296936482092838992815864935708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120729722121478592949/100000000000000000000)
  centralHi := (2414594442429571859/2000000000000000000)
  directionLo := (124445349114581326613/100000000000000000000)
  directionHi := (62222674557290663307/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree018.table
  base := (-40615562143871014360244628033742785787/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-139902046747793194644837735824000000000000)
      constant := (104041380722132270700135951390566698151140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree018.table
  base := (-516015366068243998787163710509581322881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-2156967648448610134284675373440000000000000)
      constant := (1803295488456178845520933360169543944497384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124445349114581326613/100000000000000000000)
  centralHi := (62222674557290663307/50000000000000000000)
  directionLo := (64026603902148787203/50000000000000000000)
  directionHi := (128053207804297574407/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree019.table
  base := (-435387566095926011785123509384328028461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-149316888246235718110122017748000000000000)
      constant := (136482664444537019301688706257858399549542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree019.table
  base := (-2206294481726266079808495930122567115761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-6904310303981029327893837029580000000000000)
      constant := (7004096150125718606430071093904405863811278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64026603902148787203/50000000000000000000)
  centralHi := (128053207804297574407/100000000000000000000)
  directionLo := (131562164552318031031/100000000000000000000)
  directionHi := (16445270569039753879/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree020.table
  base := (-1154973603824667979462736790384287823069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-793658648723391207877031498360000000000000)
      constant := (868281252857904051922653837995763276532236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree020.table
  base := (-2335941514666901217394181955917654022209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-7337717662616228252933647938840000000000000)
      constant := (8815045792664918786775305254756363776468782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131562164552318031031/100000000000000000000)
  centralHi := (16445270569039753879/12500000000000000000)
  directionLo := (16872491598017891047/12500000000000000000)
  directionHi := (134979932784143128377/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree021.table
  base := (-2431834907541888414689871364139595413167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-840732856215603825203452907980000000000000)
      constant := (1076638124927249061663385141465313851189474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree021.table
  base := (-2454917690758813327750769340474633806889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-2590375007083809059324486282700000000000000)
      constant := (3610924299626121076854839686918984978854474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16872491598017891047/12500000000000000000)
  centralHi := (134979932784143128377/100000000000000000000)
  directionLo := (27662654512633010689/20000000000000000000)
  directionHi := (69156636281582526723/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree022.table
  base := (-2544178104874213489174748050843753105511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-887807063707816442529874317600000000000000)
      constant := (1306572331444336861342105766796310705014642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree022.table
  base := (-5129432247034325285560824956704502508279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-8204532379886626103013269757360000000000000)
      constant := (13049510292260188411442705351411588975966321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27662654512633010689/20000000000000000000)
  centralHi := (69156636281582526723/50000000000000000000)
  directionLo := (28313629565884326303/20000000000000000000)
  directionHi := (35392036957355407879/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree023.table
  base := (-2648223142923499582276002709856396015397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-934881271200029059856295727220000000000000)
      constant := (1557363485994952555818986052121003103100534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree023.table
  base := (-5333040651957618341937285771204356270737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-8637939738521825028053080666620000000000000)
      constant := (15459101337992648565268129180219469339813063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28313629565884326303/20000000000000000000)
  centralHi := (35392036957355407879/25000000000000000000)
  directionLo := (144749851787743003699/100000000000000000000)
  directionHi := (1447498517877430037/1000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree024.table
  base := (-5489939547854685486694795520645241127951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-981955478692241677182717136840000000000000)
      constant := (1828433731785765628567551319173525314022161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree024.table
  base := (-5522564868322155968399268971252984336299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-3023782365719007984364297191960000000000000)
      constant := (6018864341504539556033105932547662580428767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144749851787743003699/100000000000000000000)
  centralHi := (1447498517877430037/1000000000000000000)
  directionLo := (73931553996406291367/50000000000000000000)
  directionHi := (29572621598562516547/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree025.table
  base := (-5670461380876305240405976995915771600233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1029029686184454294509138546460000000000000)
      constant := (2119313332521483303151277607030342007532663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree025.table
  base := (-569955681397241070745559281997203123537/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-1900950891158444575626540497028000000000000)
      constant := (4167589762701925127374166980260549351360526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73931553996406291367/50000000000000000000)
  centralHi := (29572621598562516547/20000000000000000000)
  directionLo := (150912152651848241187/100000000000000000000)
  directionHi := (37728038162962060297/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree026.table
  base := (-291967418450138135040927986103497389769/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-215220778735333382367111991216000000000000)
      constant := (485923203079966848811345012273957017427036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree026.table
  base := (-5865295201742134153365175143252956819541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-9938161814427421803172513394400000000000000)
      constant := (23799842772900081574915235226055059312373859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150912152651848241187/100000000000000000000)
  centralHi := (37728038162962060297/25000000000000000000)
  directionLo := (153900802242013462417/100000000000000000000)
  directionHi := (76950401121006731209/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree027.table
  base := (-5997710387113594419391780991459427608411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1123178101168879529161981365700000000000000)
      constant := (2759021026580632387912174104702225421169221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree027.table
  base := (-6020843276531881875177312543117797470281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-3457189724354206909404108101220000000000000)
      constant := (8979836467566213815711766103346869593266373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153900802242013462417/100000000000000000000)
  centralHi := (76950401121006731209/50000000000000000000)
  directionLo := (15683250952355485989/10000000000000000000)
  directionHi := (156832509523554859891/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree028.table
  base := (-768309568841987014009347439087987313633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1170252308661092146488402775320000000000000)
      constant := (3107259851676547072808323650236573330880504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree028.table
  base := (-308354585629050478720396747392978789393/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-2160995306339563930650427042584000000000000)
      constant := (6050926411841748214777618081953848675155228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15683250952355485989/10000000000000000000)
  centralHi := (156832509523554859891/100000000000000000000)
  directionLo := (79855205146841423149/50000000000000000000)
  directionHi := (159710410293682846299/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree029.table
  base := (-1257285963766288537961462803685233181237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-243465303230660952762964836988000000000000)
      constant := (694821243109525069896716684848967610622507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree029.table
  base := (-3152395543534470178621939167110361653531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-11238383890333018578291946122180000000000000)
      constant := (33743258491186700955981651149733898678331738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79855205146841423149/50000000000000000000)
  centralHi := (159710410293682846299/100000000000000000000)
  directionLo := (20317170335741079121/12500000000000000000)
  directionHi := (162537362685928632969/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree030.table
  base := (-1283646702815715518753571863245143955739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-252880144729103476228249118912000000000000)
      constant := (771873683587965192687474841466153396791429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree030.table
  base := (-6434576919132026558283774906833148794049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-3890597082989405834443919010480000000000000)
      constant := (12467911904452956223708312721895659995559517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20317170335741079121/12500000000000000000)
  centralHi := (162537362685928632969/100000000000000000000)
  directionLo := (33063196083632142027/20000000000000000000)
  directionHi := (20664497552270088767/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree031.table
  base := (-6542451999722295545257596455114967842649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1311474931137729998467667004180000000000000)
      constant := (4262883357875345440213654676329774293474439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree031.table
  base := (-3278494657861673101905889202006452885417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-12105198607603416428371567940700000000000000)
      constant := (41234658907540288272952867584268432090060766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33063196083632142027/20000000000000000000)
  centralHi := (20664497552270088767/12500000000000000000)
  directionLo := (33609732218116993029/20000000000000000000)
  directionHi := (84024330545292482573/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree032.table
  base := (-3329783531252545523837484308657747726767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1358549138629942615794088413800000000000000)
      constant := (4684511798985602868330274751579821813928674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree032.table
  base := (-13032204362743551790949611917665193061/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-12538605966238615353411378849960000000000000)
      constant := (45234830685481399982082688655182250418349568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33609732218116993029/20000000000000000000)
  centralHi := (84024330545292482573/50000000000000000000)
  directionLo := (21342201300716262401/12500000000000000000)
  directionHi := (170737610405730099209/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree033.table
  base := (-1353998217100662313773561643142359534457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-281124669224431046624101964684000000000000)
      constant := (1024826912512306765915842173151458094541927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree033.table
  base := (-33907340719550839574070615171412422689/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (2822)
      previous := (1513)
      next := (0)
      square := (41392837622462818683577446390000000000000)
      linear := (-864800888324920951896745983948000000000000)
      constant := (3293548543326587348648195184714217181145480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21342201300716262401/12500000000000000000)
  centralHi := (170737610405730099209/100000000000000000000)
  directionLo := (86692431503245231243/50000000000000000000)
  directionHi := (173384863006490462487/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree034.table
  base := (-6874077778479924403778807149558432595587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (280)
      previous := (145)
      next := (0)
      square := (4058121335535570459174259450000000000000)
      linear := (-85452797271433402967466543120000000000000)
      constant := (328332319204802398571883827057506645875021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree034.table
  base := (-6884264396221865128093306502451392750923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2490)
      previous := (1335)
      next := (0)
      square := (36523092019820134132568335050000000000000)
      linear := (-788554157853471364911235333440000000000000)
      constant := (3161116231434887588542627272060936909108781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86692431503245231243/50000000000000000000)
  centralHi := (173384863006490462487/100000000000000000000)
  directionLo := (175992300492095547649/100000000000000000000)
  directionHi := (3519846009841910953/2000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree035.table
  base := (-6972131017191922783698910277164289541839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1499771761106580467773352642660000000000000)
      constant := (6056968570652152662915634270189520322408529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree035.table
  base := (-6981165790992898415139991638500390138587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-13838828042144212128530811577740000000000000)
      constant := (58241323909697821728655336154630485249535213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175992300492095547649/100000000000000000000)
  centralHi := (3519846009841910953/2000000000000000000)
  directionLo := (89280833532764248869/50000000000000000000)
  directionHi := (178561667065528497739/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree036.table
  base := (-883051524260219198036111983870669794693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1546845968598793085099774052280000000000000)
      constant := (6550016452657202344094073575659011434669784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree036.table
  base := (-442026232920862484129535979547709208431/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-4757411800259803684523540829000000000000000)
      constant := (20969876197429038248578998054466177860645168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89280833532764248869/50000000000000000000)
  centralHi := (178561667065528497739/100000000000000000000)
  directionLo := (11318411448888618089/6250000000000000000)
  directionHi := (7243783327288715577/4000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree037.table
  base := (-7151146379042368205746666285350556925147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1593920176091005702426195461900000000000000)
      constant := (7060728027297726864600149195967689048632517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree037.table
  base := (-3579119300888645154580825316505988526459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-14705642759414609978610433396260000000000000)
      constant := (67743337534097560245777827787105847685360282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11318411448888618089/6250000000000000000)
  centralHi := (7243783327288715577/4000000000000000000)
  directionLo := (183592557503461518393/100000000000000000000)
  directionHi := (91796278751730759197/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree038.table
  base := (-7232527515869263160735190673786641816741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1640994383583218319752616871520000000000000)
      constant := (7589047244816827732274263045763660514961851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree038.table
  base := (-3619402440583761903741926125781990440473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-15139050118049808903650244305520000000000000)
      constant := (72741976143549314447075507485994085728659454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183592557503461518393/100000000000000000000)
  centralHi := (91796278751730759197/50000000000000000000)
  directionLo := (7442279896201960409/4000000000000000000)
  directionHi := (93028498702524505113/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree039.table
  base := (-1461744565567187377859151453462811618213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-337613718215086187415807656228000000000000)
      constant := (1626985155537692779588896565255247442336443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree039.table
  base := (-1462855078576433586168714634992735523113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (2822)
      previous := (1513)
      next := (0)
      square := (41392837622462818683577446390000000000000)
      linear := (-1038163831779000521912670347652000000000000)
      constant := (5193675767404830912563253865760098301461029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7442279896201960409/4000000000000000000)
  centralHi := (93028498702524505113/50000000000000000000)
  directionLo := (94244609124478578807/50000000000000000000)
  directionHi := (37697843649791431523/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree040.table
  base := (-7379876568005553826016850299848822798233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1735142798567643554405459690760000000000000)
      constant := (8698321936777380840014736593903690211310663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree040.table
  base := (-184619624573400760238989035598198084199/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-3201172967064041350745973224808000000000000)
      constant := (16646493580436498612667733137288694263987208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94244609124478578807/50000000000000000000)
  centralHi := (37697843649791431523/20000000000000000000)
  directionLo := (47722612897885993827/25000000000000000000)
  directionHi := (190890451591543975309/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree041.table
  base := (-744611322201713509191896223739626627881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-356443401211971234346376220076000000000000)
      constant := (1855839949146780290902020405194095809084782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree041.table
  base := (-232826551038221547449023262231605678651/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-16439272193955405678769677033300000000000000)
      constant := (88723668647973165079154332437044996154519968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47722612897885993827/25000000000000000000)
  centralHi := (190890451591543975309/100000000000000000000)
  directionLo := (3019716444900673197/1562500000000000000)
  directionHi := (193261852473643084609/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree042.table
  base := (-1501508050036554672918379765320806538499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-365858242710413757811660502000000000000000)
      constant := (1975505629705566191521425052339086910373789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree042.table
  base := (-938921140810210877381720991404373383939/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-5624226517530201534603162647520000000000000)
      constant := (31459493071180684271166382124139266208999096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3019716444900673197/1562500000000000000)
  centralHi := (193261852473643084609/100000000000000000000)
  directionLo := (195604505915034517403/100000000000000000000)
  directionHi := (48901126478758629351/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree043.table
  base := (-7564250439780119893020072424969157846639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1876365421044281406384723919620000000000000)
      constant := (10493280329635928138349311129761913382321329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree043.table
  base := (-945953665966983616488365563792390682443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-17306086911225803528849298851820000000000000)
      constant := (100196676263961612567592854786049934679726056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195604505915034517403/100000000000000000000)
  centralHi := (48901126478758629351/25000000000000000000)
  directionLo := (197919432716914797021/100000000000000000000)
  directionHi := (98959716358457398511/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree044.table
  base := (-7616323926036995666398261708240661501367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1923439628536494023711145329240000000000000)
      constant := (11126433129977352730859368592878448826104937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree044.table
  base := (-476206508734911620938550224003800532129/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-17739494269861002453889109761080000000000000)
      constant := (106178067578119399627727036504609837054919536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197919432716914797021/100000000000000000000)
  centralHi := (98959716358457398511/50000000000000000000)
  directionLo := (1564121833284432101/781250000000000000)
  directionHi := (200207594660407308929/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree045.table
  base := (-7663829930526504014850441860255802831813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-1970513836028706641037566738860000000000000)
      constant := (11776966544517477872731468822916072981606043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree045.table
  base := (-1916614295169942828987942923654381832657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-6057633876165400459642973556780000000000000)
      constant := (37440829228419819170978790050596603804345524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1564121833284432101/781250000000000000)
  centralHi := (200207594660407308929/100000000000000000000)
  directionLo := (50617474794053673141/25000000000000000000)
  directionHi := (40493979835242938513/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree046.table
  base := (-7706828257854735827138870392736744471753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2017588043520919258363988148480000000000000)
      constant := (12444863289725143297113319398987080847663383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree046.table
  base := (-1541828644847280646925087095392664913509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-3721261797426280060793746315920000000000000)
      constant := (23725958823778381205857112974014878559963091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50617474794053673141/25000000000000000000)
  centralHi := (40493979835242938513/20000000000000000000)
  directionLo := (102353601774860777109/50000000000000000000)
  directionHi := (204707203549721554219/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree047.table
  base := (-3872685292579196230998958909941195264377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2064662251013131875690409558100000000000000)
      constant := (13130108430907842311330687242487989137190094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree047.table
  base := (-774740943691500569501625434446839228601/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-3807943269153319845801708497772000000000000)
      constant := (25019972839797059248485329545057542332817598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102353601774860777109/50000000000000000000)
  centralHi := (204707203549721554219/100000000000000000000)
  directionLo := (206920318716813605079/100000000000000000000)
  directionHi := (5173007967920340127/2500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree048.table
  base := (-7779501573699516175370076396354683391201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2111736458505344493016830967720000000000000)
      constant := (13832689060960844703416192091821496499942911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree048.table
  base := (-3890648220534054481646360208107434218379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-6491041234800599384682784466040000000000000)
      constant := (43910864088933565643351790238565709065330814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206920318716813605079/100000000000000000000)
  centralHi := (5173007967920340127/2500000000000000000)
  directionLo := (5227750317451828663/2500000000000000000)
  directionHi := (209110012698073146521/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree049.table
  base := (-3904629913752064767011241680603428151049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2158810665997557110343252377340000000000000)
      constant := (14552594023320629951574131284901218528693678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree049.table
  base := (-7810839228773263882019115403456007950497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-19906531063036997079088164307380000000000000)
      constant := (138527887307944398350662037110332923320757303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5227750317451828663/2500000000000000000)
  centralHi := (209110012698073146521/100000000000000000000)
  directionLo := (211277013712587537661/100000000000000000000)
  directionHi := (105638506856293768831/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree050.table
  base := (-7834678720359942448073343381064136691111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2205884873489769727669673786960000000000000)
      constant := (15289813672962549891780343673072464496268921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree050.table
  base := (-3918033973790100418718653401383100920917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-20339938421672196004127975216640000000000000)
      constant := (145485670908639551769631549550605109009389766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211277013712587537661/100000000000000000000)
  centralHi := (105638506856293768831/50000000000000000000)
  directionLo := (213422013007162624011/100000000000000000000)
  directionHi := (53355503251790656003/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree051.table
  base := (-3927893554714623921917026850287932522117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (280)
      previous := (145)
      next := (0)
      square := (4058121335535570459174259450000000000000)
      linear := (-132527004763646020293887952740000000000000)
      constant := (943784686480394227548872673684210294248022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree051.table
  base := (-1964252144057969671718460354689419287749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (830)
      previous := (445)
      next := (0)
      square := (12174364006606711377522778350000000000000)
      linear := (-407320505496223429983682080900000000000000)
      constant := (2992272068591680807824658035249358465299204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213422013007162624011/100000000000000000000)
  centralHi := (53355503251790656003/25000000000000000000)
  directionLo := (26943208429012681953/12500000000000000000)
  directionHi := (344873067891362329/160000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree052.table
  base := (-7872609951142473854647053255524675781309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2300033288474194962322516606200000000000000)
      constant := (16816164802524692150689641771137368699201699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree052.table
  base := (-1968420876462490769793112696888121619001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-21206753138942593854207597035160000000000000)
      constant := (159888442837245454286297522126215982675913596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26943208429012681953/12500000000000000000)
  centralHi := (344873067891362329/160000000000000000)
  directionLo := (10882430089537753603/5000000000000000000)
  directionHi := (217648601790755072061/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree053.table
  base := (-7885168832834421221833224176898003183403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2347107495966407579648938015820000000000000)
      constant := (17605282831296763324615027692734477079996533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree053.table
  base := (-3943056019933419255663354247754747545311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-21640160497577792779247407944420000000000000)
      constant := (167333322717621118954671151637981803269292178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10882430089537753603/5000000000000000000)
  centralHi := (217648601790755072061/100000000000000000000)
  directionLo := (54932852746666578547/25000000000000000000)
  directionHi := (219731410986666314189/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree054.table
  base := (-7893482431704736657365666742453004025061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2394181703458620196975359425440000000000000)
      constant := (18411688358772217490346767237151081836757371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree054.table
  base := (-7894310824102104029130439009045580876409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-7357855952070997234762406284560000000000000)
      constant := (58313490614508646028689570298621481380153397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54932852746666578547/25000000000000000000)
  centralHi := (219731410986666314189/100000000000000000000)
  directionLo := (110897330994609437051/50000000000000000000)
  directionHi := (221794661989218874103/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree055.table
  base := (-7897566911075036037633420755549045720979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2441255910950832814301780835060000000000000)
      constant := (19235376713751107659608427901216325786637069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree055.table
  base := (-61705423568521942875949694908719540903/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-22506975214848190629327029762940000000000000)
      constant := (182709852869242569087036073568839820686246016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110897330994609437051/50000000000000000000)
  centralHi := (221794661989218874103/100000000000000000000)
  directionLo := (27979861954524666639/12500000000000000000)
  directionHi := (223838895636197333113/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree056.table
  base := (-7897436262535275994544060529733033781721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2488330118443045431628202244680000000000000)
      constant := (20076343852663936365778720708315153237082631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree056.table
  base := (-987259325853956215686655056853713006901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-22940382573483389554366840672200000000000000)
      constant := (190641433571089440443633814522843939752403992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27979861954524666639/12500000000000000000)
  centralHi := (223838895636197333113/100000000000000000000)
  directionLo := (45172925657899569497/20000000000000000000)
  directionHi := (112932314144748923743/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree057.table
  base := (-197327565034672110250109222450618804343/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-507080865187051609790924730860000000000000)
      constant := (4186917254837718190197317083940969324358984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree057.table
  base := (-7893662687901277226748621727882055468099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-7791263310706196159802217193820000000000000)
      constant := (66245062044989881761156085231836257909158167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45172925657899569497/20000000000000000000)
  centralHi := (112932314144748923743/50000000000000000000)
  directionLo := (227872353358351967469/100000000000000000000)
  directionHi := (22787235335835196747/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree058.table
  base := (-985572052721380559318235902813237984213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2582478533427470666281045063920000000000000)
      constant := (21810100945518269473168406581743793780499544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree058.table
  base := (-246408365435833881217314592610726793871/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-23807197290753787404446462490720000000000000)
      constant := (206991086543335034795159789014855987492528928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227872353358351967469/100000000000000000000)
  centralHi := (22787235335835196747/10000000000000000000)
  directionLo := (229862542702794904571/100000000000000000000)
  directionHi := (57465635675698726143/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree059.table
  base := (-3935933408496645987656866110959830598887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2629552740919683283607466473540000000000000)
      constant := (22702885238687672089839245462715217913843314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree059.table
  base := (-492018600131060088413726362234370727083/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-24240604649388986329486273399980000000000000)
      constant := (215409114047672843879409785787016427821713872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229862542702794904571/100000000000000000000)
  centralHi := (57465635675698726143/25000000000000000000)
  directionLo := (11591782396434424191/5000000000000000000)
  directionHi := (231835647928688483821/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree060.table
  base := (-7854981669799916639686617016272306191469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2676626948411895900933887883160000000000000)
      constant := (23612936875583121069786653970937303510665459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree060.table
  base := (-981919913395972097425551391279007475963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-8224670669341395084842028103080000000000000)
      constant := (74663083571522506771199620710728804146720632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11591782396434424191/5000000000000000000)
  centralHi := (231835647928688483821/100000000000000000000)
  directionLo := (4675842031687357623/2000000000000000000)
  directionHi := (233792101584367881151/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree061.table
  base := (-7833927816710336543090318837887181491007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2723701155904108518260309292780000000000000)
      constant := (24540253880450504589212582486268604549098977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree061.table
  base := (-1958564692962307600583241282213919825357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-25107419366659384179565895218500000000000000)
      constant := (232731481035062113714154215099352378136985772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4675842031687357623/2000000000000000000)
  centralHi := (233792101584367881151/100000000000000000000)
  directionLo := (117866159133947328021/50000000000000000000)
  directionHi := (235732318267894656043/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree062.table
  base := (-39043555949739920876831090182208485501/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-554155072679264227117346140480000000000000)
      constant := (5096966907775450131710574417530469907608440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree062.table
  base := (-390450057797763602092374179733803157071/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-5108165345058916620921141225552000000000000)
      constant := (48327158317696108151873536600153511953833316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117866159133947328021/50000000000000000000)
  centralHi := (235732318267894656043/100000000000000000000)
  directionLo := (237656695652945091633/100000000000000000000)
  directionHi := (118828347826472545817/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree063.table
  base := (-1944834235006947335185900009050668707333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2817849570888533752913152112020000000000000)
      constant := (26446677362364544564385259287475426974323052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree063.table
  base := (-1555918185531573398080312477525178661601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (2822)
      previous := (1513)
      next := (0)
      square := (41392837622462818683577446390000000000000)
      linear := (-1731615605595318801976367802468000000000000)
      constant := (16713478050207167981571164200316470100391933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237656695652945091633/100000000000000000000)
  centralHi := (118828347826472545817/50000000000000000000)
  directionLo := (29945701930065533681/12500000000000000000)
  directionHi := (239565615440524269449/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree064.table
  base := (-484113096352522145229626765812526091631/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2864923778380746370239573521640000000000000)
      constant := (27425781057726802246503242258562879352298256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree064.table
  base := (-7746031959220627196952711164627243769117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-26407641442564980954685327946280000000000000)
      constant := (259930608457185395927515072493636538956526683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29945701930065533681/12500000000000000000)
  centralHi := (239565615440524269449/100000000000000000000)
  directionLo := (241459444242957185899/100000000000000000000)
  directionHi := (2414594442429571859/1000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree065.table
  base := (-3854066442556100498207861881939873140881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2911997985872958987565994931260000000000000)
      constant := (28422144500659658883824195109648753324570782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree065.table
  base := (-7708327609395321543272711140219046287043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-26841048801200179879725138855540000000000000)
      constant := (269321095964600818509722108528420260607401157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241459444242957185899/100000000000000000000)
  centralHi := (2414594442429571859/1000000000000000000)
  directionLo := (60834633601488849987/25000000000000000000)
  directionHi := (243338534405955399949/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree066.table
  base := (-3833155177705066427702643662415648164881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-2959072193365171604892416340880000000000000)
      constant := (29435766712907708265877940222251755360698782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree066.table
  base := (-7666480794342512034558365531095374638089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-9091485386611792934921649921600000000000000)
      constant := (92957875230140055231557228647492310188776837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60834633601488849987/25000000000000000000)
  centralHi := (243338534405955399949/100000000000000000000)
  directionLo := (61300806193494984999/25000000000000000000)
  directionHi := (245203224773979939997/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree067.table
  base := (-1524068980077801336233945609555608198553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-601229280171476844443767550100000000000000)
      constant := (6093329368508179356618434392605229230618183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree067.table
  base := (-1524098809735527844048040766498616088599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-5541572703694115545960952134812000000000000)
      constant := (57717638208421735322658999503739099553554001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61300806193494984999/25000000000000000000)
  centralHi := (245203224773979939997/100000000000000000000)
  directionLo := (247053841403608860463/100000000000000000000)
  directionHi := (15440865087725553779/6250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree068.table
  base := (-946279886218775296141861365099526063451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (280)
      previous := (145)
      next := (0)
      square := (4058121335535570459174259450000000000000)
      linear := (-179601212255858637620309362360000000000000)
      constant := (1853810832171501508569930654730464455370664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree068.table
  base := (-1514073915604056391431826719100815054913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (498)
      previous := (267)
      next := (0)
      square := (7304618403964026826513667010000000000000)
      linear := (-331073775024773842998171430392000000000000)
      constant := (3511350426857056784222927561372775296598311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247053841403608860463/100000000000000000000)
  centralHi := (15440865087725553779/6250000000000000000)
  directionLo := (124445349114581326613/50000000000000000000)
  directionHi := (248890698229162653227/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree069.table
  base := (-1878998791494444682431623726612661002857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3100294815841809456871680569740000000000000)
      constant := (32580177977953701857454854944245763880697308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree069.table
  base := (-3758054652115979419182176524761409728529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-9524892745246991859961460830860000000000000)
      constant := (102834468804627268657037418980597715530730714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124445349114581326613/50000000000000000000)
  centralHi := (248890698229162653227/100000000000000000000)
  directionLo := (250714097684435566189/100000000000000000000)
  directionHi := (25071409768443556619/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree070.table
  base := (-7457615088346366012427700896692873798663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3147369023334022074198101979360000000000000)
      constant := (33662827769425057276289639906735759472186393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree070.table
  base := (-7457714904362351076594120622307808506449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-29008085594376174504924193401840000000000000)
      constant := (318704047073198393715453030023417390074726151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250714097684435566189/100000000000000000000)
  centralHi := (25071409768443556619/10000000000000000000)
  directionLo := (252524331284019618087/100000000000000000000)
  directionHi := (31565541410502452261/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree071.table
  base := (-115548446421023882047261492532793420623/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3194443230826234691524523388980000000000000)
      constant := (34762733025957707838628956521651452892156992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree071.table
  base := (-7395187844181452397902516768970035775159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-29441492953011373429964004311100000000000000)
      constant := (329066704448331836210504498697814936948811441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252524331284019618087/100000000000000000000)
  centralHi := (31565541410502452261/12500000000000000000)
  directionLo := (254321680167385413219/100000000000000000000)
  directionHi := (12716084008369270661/5000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree072.table
  base := (-732845311553640243047355156643512439541/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-648303487663689461770188959720000000000000)
      constant := (7175978662708537025844106886896849809945302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree072.table
  base := (-7328529407052660116606555134672610308307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-9958300103882190785001271740120000000000000)
      constant := (113197125067084645680576036824638846862697831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254321680167385413219/100000000000000000000)
  centralHi := (12716084008369270661/5000000000000000000)
  directionLo := (256106415608595148813/100000000000000000000)
  directionHi := (128053207804297574407/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree073.table
  base := (-1451534807989018216242500609292152440149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-657718329162131985235473241644000000000000)
      constant := (7402861650265649068673537866878167944796939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree073.table
  base := (-1814435179699108716252901931701298264137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-30308307670281771280043626129620000000000000)
      constant := (350278056403705678104497592760501692859918652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256106415608595148813/100000000000000000000)
  centralHi := (128053207804297574407/50000000000000000000)
  directionLo := (25787879949426447319/10000000000000000000)
  directionHi := (257878799494264473191/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree074.table
  base := (-1795691125650292280234731040787173719211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3335665853302872543503787617840000000000000)
      constant := (38165977504528241387655891637290027180592084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree074.table
  base := (-287312910764139398542689365555993276987/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-6148343005783394041016687407776000000000000)
      constant := (72225349096300305411464728210958707432784065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25787879949426447319/10000000000000000000)
  centralHi := (257878799494264473191/100000000000000000000)
  directionLo := (259639084772157615459/100000000000000000000)
  directionHi := (12981954238607880773/5000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree075.table
  base := (-3551862761873323332610173778960483354931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3382740060795085160830209027460000000000000)
      constant := (39334900778292732338686124409810840620849882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree075.table
  base := (-1420755285995683957598883087384398527523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (2822)
      previous := (1513)
      next := (0)
      square := (41392837622462818683577446390000000000000)
      linear := (-2078341492503477942008216529876000000000000)
      constant := (24809162677770499660930398906947726476637559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259639084772157615459/100000000000000000000)
  centralHi := (12981954238607880773/5000000000000000000)
  directionLo := (5227750317451828663/2000000000000000000)
  directionHi := (261387515872591433151/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree076.table
  base := (-877569750471133190021663775204875707979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3429814268287297778156630437080000000000000)
      constant := (40521077812409718614490708467374327363152552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree076.table
  base := (-351030123581384832780871576898697990619/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-6321705949237473611032611771480000000000000)
      constant := (76662027691113317238406833668877146105599924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5227750317451828663/2000000000000000000)
  centralHi := (261387515872591433151/100000000000000000000)
  directionLo := (131562164552318031031/50000000000000000000)
  directionHi := (263124329104636062063/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree077.table
  base := (-6933262739050509120891419917466344742953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3476888475779510395483051846700000000000000)
      constant := (41724508376724778102327591149086226369286583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree077.table
  base := (-866662697018492088310141238640199910543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-32041937104822566980202869766660000000000000)
      constant := (394644838574395489306301547013464720261421256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131562164552318031031/50000000000000000000)
  centralHi := (263124329104636062063/100000000000000000000)
  directionLo := (66212438257232595519/25000000000000000000)
  directionHi := (264849753028930382077/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree078.table
  base := (-3420920217835431075479172906801730850319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3523962683271723012809473256320000000000000)
      constant := (42945192267180824128641092082676599568515618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree078.table
  base := (-6841874349320998475390045134646617931973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-10825114821152588635080893558640000000000000)
      constant := (135380512982468530069243841719245382252979409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66212438257232595519/25000000000000000000)
  centralHi := (264849753028930382077/100000000000000000000)
  directionLo := (53312801761755499747/20000000000000000000)
  directionHi := (16660250550548593671/6250000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree079.table
  base := (-210821616289297024611674579903192865829/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3571036890763935630135894665940000000000000)
      constant := (44183129302393543822220556153425272376813408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree079.table
  base := (-843290166347430948696911163307807549041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-32908751822092964830282491585180000000000000)
      constant := (417800238171012585699895980226133140519554872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53312801761755499747/20000000000000000000)
  centralHi := (16660250550548593671/6250000000000000000)
  directionLo := (134133655270523547477/50000000000000000000)
  directionHi := (53653462108209418991/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree080.table
  base := (-415413572202110860897830222133394676541/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3618111098256148247462316075560000000000000)
      constant := (45438319320689592864157450494775183015674416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree080.table
  base := (-6646643002769278757135172823672335145319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-33342159180728163755322302494440000000000000)
      constant := (429620934990894643547031206870588256287025281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134133655270523547477/50000000000000000000)
  centralHi := (53653462108209418991/20000000000000000000)
  directionLo := (16872491598017891047/6250000000000000000)
  directionHi := (269959865568286256753/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree081.table
  base := (-3271408618842054201138106115375756455573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3665185305748360864788737485180000000000000)
      constant := (46710762177544568299369313008770812768678806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree081.table
  base := (-6542839797705098660312262201039127989439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-11258522179787787560120704467900000000000000)
      constant := (147201209427447123922874763195401076033156387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16872491598017891047/6250000000000000000)
  centralHi := (269959865568286256753/100000000000000000000)
  directionLo := (33955234346665854267/12500000000000000000)
  directionHi := (271641874773326834137/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree082.table
  base := (-6434892417024081631715034554041075422917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3712259513240573482115158894800000000000000)
      constant := (48000457743366369542298040386866129202776987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree082.table
  base := (-6434912104685748619286359672081577861759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-34208973897998561605401924312960000000000000)
      constant := (453748317033306684090887562763595815981564841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33955234346665854267/12500000000000000000)
  centralHi := (271641874773326834137/100000000000000000000)
  directionLo := (1708209580359839613/625000000000000000)
  directionHi := (273313532857574338081/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree083.table
  base := (-252913723865514160626155037543547987931/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-751866744146557219888316060884000000000000)
      constant := (9861481180315394838626937676849173157439705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree083.table
  base := (-6322860275114917135763639166454084402197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-34642381256633760530441735222220000000000000)
      constant := (466055000329789586720883268011734926469885603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1708209580359839613/625000000000000000)
  centralHi := (273313532857574338081/100000000000000000000)
  directionLo := (68743757151017428391/25000000000000000000)
  directionHi := (54995005720813942713/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree084.table
  base := (-6206669640623427286103022882227384798071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3806407928224998716768001714040000000000000)
      constant := (50631606546952059751328284203036285793357481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree084.table
  base := (-6206684627551133974596608999606027635511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-11691929538422986485160515377160000000000000)
      constant := (159507892447739781246743343734045574040011963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68743757151017428391/25000000000000000000)
  centralHi := (54995005720813942713/20000000000000000000)
  directionLo := (27662654512633010689/10000000000000000000)
  directionHi := (276626545126330106891/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree085.table
  base := (-6086372378766937502893249835313107682827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (280)
      previous := (145)
      next := (0)
      square := (4058121335535570459174259450000000000000)
      linear := (-226675419748071254946730771980000000000000)
      constant := (3057238799069613699740454942769677169391941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree085.table
  base := (-6086385451894192706999783809007408551681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2490)
      previous := (1335)
      next := (0)
      square := (36523092019820134132568335050000000000000)
      linear := (-2088776233759068140030668061220000000000000)
      constant := (28891432195268623062952876456631866491592807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27662654512633010689/10000000000000000000)
  centralHi := (276626545126330106891/100000000000000000000)
  directionLo := (55653652020779422291/20000000000000000000)
  directionHi := (8695883128246784733/3125000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree086.table
  base := (-1490487902712675457503425432522733559659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3900556343209423951420844533280000000000000)
      constant := (53331764926634003965520174970971720005034196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree086.table
  base := (-5961963013000124782122114777387651169057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-35942603332539357305561167950000000000000000)
      constant := (503947009569940793911553451667270719309282743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55653652020779422291/20000000000000000000)
  centralHi := (8695883128246784733/3125000000000000000)
  directionLo := (55980069201090034631/20000000000000000000)
  directionHi := (69975086501362543289/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree087.table
  base := (-5833407610385461929339541385176781871971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3947630550701636568747265942900000000000000)
      constant := (54707722495259168620843684980117910039000381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree087.table
  base := (-5833417553804007225524201432421620535311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-12125336897058185410200326286420000000000000)
      constant := (172300554487489271306936855848080454995885363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55980069201090034631/20000000000000000000)
  centralHi := (69975086501362543289/25000000000000000000)
  directionLo := (281522970300278191259/100000000000000000000)
  directionHi := (14076148515013909563/5000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree088.table
  base := (-1425185156961235728815696678800999708999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-3994704758193849186073687352520000000000000)
      constant := (56100932217672020303498970877194044336397156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree088.table
  base := (-712593662252354648132949883704071689843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-36809418049809755155640789768520000000000000)
      constant := (530018308415270146516392746069997676277746856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281522970300278191259/100000000000000000000)
  centralHi := (14076148515013909563/5000000000000000000)
  directionLo := (28313629565884326303/10000000000000000000)
  directionHi := (283136295658843263031/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree089.table
  base := (-2781975446735102034843817899264311104199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4041778965686061803400108762140000000000000)
      constant := (57511394027332892881015719417555228181772978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree089.table
  base := (-5563958452469199560165976901374385115127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-37242825408444954080680600677780000000000000)
      constant := (543296943890397046374893821623207224315554673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28313629565884326303/10000000000000000000)
  centralHi := (283136295658843263031/100000000000000000000)
  directionLo := (14237024007155822753/5000000000000000000)
  directionHi := (284740480143116455061/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree090.table
  base := (-5423038619702066617665756842040045086547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4088853173178274420726530171760000000000000)
      constant := (58939107862846389019353998489410426969987917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree090.table
  base := (-2711522604555136798019064691977766435997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-12558744255693384335240137195680000000000000)
      constant := (185579189796191030759843640607670552999981202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14237024007155822753/5000000000000000000)
  centralHi := (284740480143116455061/100000000000000000000)
  directionLo := (143167838693657981481/50000000000000000000)
  directionHi := (286335677387315962963/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree091.table
  base := (-2639002001645983335310513830497211824461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4135927380670487038052951581380000000000000)
      constant := (60384073667351343682312307404150611565461542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree091.table
  base := (-5278009746775685392055279604663229228091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-38109640125715351930760222496300000000000000)
      constant := (570340184444652022745829091419376940777735309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143167838693657981481/50000000000000000000)
  centralHi := (286335677387315962963/100000000000000000000)
  directionLo := (287922036769632615647/100000000000000000000)
  directionHi := (8997563649051019239/3125000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree092.table
  base := (-2564423613567363430841592528408642279161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4183001588162699655379372991000000000000000)
      constant := (61846291387991153128916152226163804762644942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree092.table
  base := (-1282213058172914103691553449022582615357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-38543047484350550855800033405560000000000000)
      constant := (584104788623678435739294937421329050469825772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287922036769632615647/100000000000000000000)
  centralHi := (8997563649051019239/3125000000000000000)
  directionLo := (144749851787743003699/50000000000000000000)
  directionHi := (289499703575486007399/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree093.table
  base := (-497556846186082048376726493089726333359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-846015159130982454541158880124000000000000)
      constant := (12665152195090722115502617515989738179318498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree093.table
  base := (-2487786411894843110460753531136299885193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-12992151614328583260279948104940000000000000)
      constant := (199343793839157833637606737994423655999075338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144749851787743003699/50000000000000000000)
  centralHi := (289499703575486007399/100000000000000000000)
  directionLo := (58213763830563251297/20000000000000000000)
  directionHi := (145534409576408128243/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree094.table
  base := (-96363357344411790367777805578128255721/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-855430000629424978006443162048000000000000)
      constant := (12964496476714173439089019683951209340966310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree094.table
  base := (-192726866713820909082683035822498805667/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-7881972440324189741175931044816000000000000)
      constant := (122423992548334499587093798461718803032300665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58213763830563251297/20000000000000000000)
  centralHi := (145534409576408128243/50000000000000000000)
  directionLo := (292629521059881184139/100000000000000000000)
  directionHi := (14631476052994059207/5000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree095.table
  base := (-186265823731538505900252818213015266549/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-864844842127867501471727443972000000000000)
      constant := (13267291113794282618725249558428192939836695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree095.table
  base := (-4656648904468314021832030156809961946637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-39843269560256147630919466133340000000000000)
      constant := (626370531933152032628716957649227288976797163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292629521059881184139/100000000000000000000)
  centralHi := (14631476052994059207/5000000000000000000)
  directionLo := (294181943205996304589/100000000000000000000)
  directionHi := (29418194320599630459/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree096.table
  base := (-4491001781511406043646295471342361852609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4371298418131550124685058629480000000000000)
      constant := (67867680490777075048196307833870057424595999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree096.table
  base := (-1122751166490128646830124849118367821521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-13425558972963782185319759014200000000000000)
      constant := (213594362915931140294870423014809500394965172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294181943205996304589/100000000000000000000)
  centralHi := (29418194320599630459/10000000000000000000)
  directionLo := (295726215985625165469/100000000000000000000)
  directionHi := (29572621598562516547/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree097.table
  base := (-1080309141405636572704725652054591685773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4418372625623762742011480039100000000000000)
      constant := (69416157110338979476376363320658892011246412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree097.table
  base := (-4321239078066260750901863597032633843499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-40710084277526545480999087951860000000000000)
      constant := (655357632858536164115664169159768119373059101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295726215985625165469/100000000000000000000)
  centralHi := (29572621598562516547/10000000000000000000)
  directionLo := (59452493281240010583/20000000000000000000)
  directionHi := (74315616601550013229/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree098.table
  base := (-4147350072438060267413327073445035230709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4465446833115975359337901448720000000000000)
      constant := (70981885391007251260311939727542384818325099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree098.table
  base := (-414735226062347059132039900154902744007/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-8228698327232348881207779772224000000000000)
      constant := (134018832790736367479812359097408595925675586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59452493281240010583/20000000000000000000)
  centralHi := (74315616601550013229/25000000000000000000)
  directionLo := (59758163642005534723/20000000000000000000)
  directionHi := (18674426138126729601/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree099.table
  base := (-3969342422552969971061193212695029676283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4512521040608187976664322858340000000000000)
      constant := (72564865297929929042687497618621136423554213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree099.table
  base := (-992336082033201690365172943684123944903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-13858966331598981110359569923460000000000000)
      constant := (228330893911804739058217113137277458159076396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59758163642005534723/20000000000000000000)
  centralHi := (18674426138126729601/6250000000000000000)
  directionLo := (4692365499853296303/1562500000000000000)
  directionHi := (300311391990610963393/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree100.table
  base := (-3787213730949358192670176616075956461137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4559595248100400593990744267960000000000000)
      constant := (74165096797877190896930718748354048582731407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree100.table
  base := (-3787215390254818916721407838962671321029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-42010306353432142256118520679640000000000000)
      constant := (700053185918506213788740870870058091894003571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4692365499853296303/1562500000000000000)
  centralHi := (300311391990610963393/100000000000000000000)
  directionLo := (150912152651848241187/50000000000000000000)
  directionHi := (2414594442429571859/800000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree101.table
  base := (-3600964107528687979828862903550606056439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4606669455592613211317165677580000000000000)
      constant := (75782579859087514002288501872571874849689129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree101.table
  base := (-900241388061253621463275956877005697683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-42443713712067341181158331588900000000000000)
      constant := (715275676229188252419150192058557632721306068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150912152651848241187/50000000000000000000)
  centralHi := (2414594442429571859/800000000000000000)
  directionLo := (151664836386668395061/50000000000000000000)
  directionHi := (303329672773336790123/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree102.table
  base := (-852648414394581382313621707939025418957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (280)
      previous := (145)
      next := (0)
      square := (4058121335535570459174259450000000000000)
      linear := (-273749627240283872273152181600000000000000)
      constant := (4553959673596049972229974479212146271510924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree102.table
  base := (-3410594915335256970880049026669461275673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (830)
      previous := (445)
      next := (0)
      square := (12174364006606711377522778350000000000000)
      linear := (-840727864131422355023492990160000000000000)
      constant := (14326669654983456001904199579679857474940677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151664836386668395061/50000000000000000000)
  centralHi := (303329672773336790123/100000000000000000000)
  directionLo := (304827606193238614013/100000000000000000000)
  directionHi := (152413803096619307007/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree103.table
  base := (-3216102482180998457257476602897753621849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4700817870577038445970008496820000000000000)
      constant := (79069300544800289192680197820020549203285639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree103.table
  base := (-402012947133591167505192894005016276647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-43310528429337739031237953407420000000000000)
      constant := (746206614189700405922242411825145621315529224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304827606193238614013/100000000000000000000)
  centralHi := (152413803096619307007/50000000000000000000)
  directionLo := (153159107311825203517/50000000000000000000)
  directionHi := (61263642924730081407/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree104.table
  base := (-3017490678574739907720787356824852182267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4747892078069251063296429906440000000000000)
      constant := (80738538111988041418018222857397617719324837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree104.table
  base := (-3017491631594700162934209460363647714661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-43743935787972937956277764316680000000000000)
      constant := (761915061340938454345014074752186152294166739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153159107311825203517/50000000000000000000)
  centralHi := (61263642924730081407/20000000000000000000)
  directionLo := (153900802242013462417/50000000000000000000)
  directionHi := (61560320896805384967/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree105.table
  base := (-87961198139682758548239710532459677243/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4794966285561463680622851316060000000000000)
      constant := (82425027125613829968375757533765812904856736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree105.table
  base := (-703689792482117342727126394990185511549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-14725781048869378960439191741980000000000000)
      constant := (259261831207046535414662209017844036645948068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153900802242013462417/50000000000000000000)
  centralHi := (61560320896805384967/20000000000000000000)
  directionLo := (309277879641693634277/100000000000000000000)
  directionHi := (154638939820846817139/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree106.table
  base := (-260790555832851050050691589261775027433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-968408098610735259589854545136000000000000)
      constant := (16825753511906816563284430757008294034143726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree106.table
  base := (-2607906280181129498586427127080214838597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-44610750505243335806357386135200000000000000)
      constant := (793817910801126909936608258131320361204809203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309277879641693634277/100000000000000000000)
  centralHi := (154638939820846817139/50000000000000000000)
  directionLo := (310747141496720004199/100000000000000000000)
  directionHi := (1553735707483600021/500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree107.table
  base := (-599233104902993768767677951478760463939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4889114700545888915275694135300000000000000)
      constant := (85849759388472499149570416995324552903686516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree107.table
  base := (-2396933047763140273792791969979734462747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-45044157863878534731397197044460000000000000)
      constant := (810012312658747759670806616710212710662395053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310747141496720004199/100000000000000000000)
  centralHi := (1553735707483600021/500000000000000000)
  directionLo := (312209489063197938953/100000000000000000000)
  directionHi := (156104744531598969477/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree108.table
  base := (-1090919504499751258571019721883575848333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-4936188908038101532602115544920000000000000)
      constant := (87588002587956772677567429665199293159663526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree108.table
  base := (-2181839555565165104450825303785307180697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-15159188407504577885479002651240000000000000)
      constant := (275456232992801179974191131352562138674335701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312209489063197938953/100000000000000000000)
  centralHi := (156104744531598969477/50000000000000000000)
  directionLo := (15683250952355485989/5000000000000000000)
  directionHi := (313665019047109719781/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree109.table
  base := (-392525081716550476780055975182467918001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-996652623106062829985707390908000000000000)
      constant := (17868699426852482757677670133102266771697711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree109.table
  base := (-981312942059572499376911866601613389769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-45910972581148932581476818862980000000000000)
      constant := (842887069550630672129597825704900407146421662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15683250952355485989/5000000000000000000)
  centralHi := (313665019047109719781/100000000000000000000)
  directionLo := (315113825920958747683/100000000000000000000)
  directionHi := (78778456480239686921/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree110.table
  base := (-217411462254846780879490590275406265937/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5030337323022526767254958364160000000000000)
      constant := (91116243004362755155814627918123260713153656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree110.table
  base := (-434823027935544527955279068594840096659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-46344379939784131506516629772240000000000000)
      constant := (859567424171726383990414536880859283634359764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315113825920958747683/100000000000000000000)
  centralHi := (78778456480239686921/25000000000000000000)
  directionLo := (316556001995326070287/100000000000000000000)
  directionHi := (19784750124707879393/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree111.table
  base := (-37795948869608632563140742470586546461/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-1015482306102947876916275954756000000000000)
      constant := (18581248035176869634041801584211603904582168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree111.table
  base := (-1511838314665422285181998183710581815169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-15592595766139776810518813560500000000000000)
      constant := (292136587547804477986401943541224925566248477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316556001995326070287/100000000000000000000)
  centralHi := (19784750124707879393/6250000000000000000)
  directionLo := (317991637487506065451/100000000000000000000)
  directionHi := (79497909371876516363/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree112.table
  base := (-1280264254114030115562367214337319855011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5124485738006952001907801183400000000000000)
      constant := (94713488627067063672230721648240514561901821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree112.table
  base := (-1280264567149935759508400430846681731307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-47211194657054529356596251590760000000000000)
      constant := (893414084772538809551984014481287780816870493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317991637487506065451/100000000000000000000)
  centralHi := (79497909371876516363/25000000000000000000)
  directionLo := (319420820587365692597/100000000000000000000)
  directionHi := (159710410293682846299/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree113.table
  base := (-1044570669324020640235981890975365692621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5171559945499164619234222593020000000000000)
      constant := (96537988336728302187147804003846119314832531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree113.table
  base := (-1044570941591110919668194426941083276919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-47644602015689728281636062500020000000000000)
      constant := (910580390370802095175707754913288242396733681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319420820587365692597/100000000000000000000)
  centralHi := (159710410293682846299/50000000000000000000)
  directionLo := (78330966191543789/24414062500000000)
  directionHi := (64168727504112671949/20000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree114.table
  base := (-50297329488971268884391145243161570317/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5218634152991377236560644002640000000000000)
      constant := (98379739284230798144960761239875620898854192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree114.table
  base := (-804757508613131643686521633240611088287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-16026003124774975735558624469760000000000000)
      constant := (309302893084836596187877886326324390186455171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78330966191543789/24414062500000000)
  centralHi := (64168727504112671949/20000000000000000000)
  directionLo := (322260172609255645161/100000000000000000000)
  directionHi := (161130086304627822581/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree115.table
  base := (-560824131235358735545649820691619126029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5265708360483589853887065412260000000000000)
      constant := (100238741449453571121374102350430122072577619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree115.table
  base := (-56082433715469155638788196454418429801/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (8466)
      previous := (4539)
      next := (0)
      square := (124178512867388456050732339170000000000000)
      linear := (-9702283346592025226343136863708000000000000)
      constant := (189079790248870469519518640479990115328175198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322260172609255645161/100000000000000000000)
  centralHi := (161130086304627822581/50000000000000000000)
  directionLo := (323670508330412816157/100000000000000000000)
  directionHi := (161835254165206408079/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree116.table
  base := (-39096414435844833341063804682818072487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5312782567975802471213486821880000000000000)
      constant := (102114994812765636408485291013301324616410056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree116.table
  base := (-312771494547043917170425667281294317701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-48944824091595325056755495227800000000000000)
      constant := (963051206165201182549891796385257353479659699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323670508330412816157/100000000000000000000)
  centralHi := (161835254165206408079/50000000000000000000)
  directionLo := (20317170335741079121/6250000000000000000)
  directionHi := (325074725371857265937/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree117.table
  base := (-15149722723029766150379079403394484939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5359856775468015088539908231500000000000000)
      constant := (104008499355002138484281453823043675975410516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree117.table
  base := (-60599046585310284652475260417644071083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-16459410483410174660598435379020000000000000)
      constant := (326955147948641060748854394687687902590371039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20317170335741079121/6250000000000000000)
  centralHi := (325074725371857265937/100000000000000000000)
  directionLo := (32647290268613260809/10000000000000000000)
  directionHi := (326472902686132608091/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree118.table
  base := (39138615554374947153445332199997633711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-1081386196592045541173265928224000000000000)
      constant := (21183851011488523057385581636191399316142479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree118.table
  base := (195692942406148698083306361463459188717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-49811638808865722906835117046320000000000000)
      constant := (998841664119210684654949359244558457349852917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32647290268613260809/10000000000000000000)
  centralHi := (326472902686132608091/100000000000000000000)
  directionLo := (327865117542305195069/100000000000000000000)
  directionHi := (32786511754230519507/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree119.table
  base := (114026131799378986799550215569221889819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (280)
      previous := (145)
      next := (0)
      square := (4058121335535570459174259450000000000000)
      linear := (-320823834732496489599573591220000000000000)
      constant := (6343956582458302326760574911188707088507692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree119.table
  base := (456104409513603815982528995179878265721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2490)
      previous := (1335)
      next := (0)
      square := (36523092019820134132568335050000000000000)
      linear := (-2955590951029465990110289879740000000000000)
      constant := (59822345107142651769805520765368521374655313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327865117542305195069/100000000000000000000)
  centralHi := (32786511754230519507/10000000000000000000)
  directionLo := (329251445575794232687/100000000000000000000)
  directionHi := (20578215348487139543/6250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree120.table
  base := (90079424435386640643497508792305413423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5501079397944652940519172460360000000000000)
      constant := (109792519870158116680813999574407810115833976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree120.table
  base := (720635293178464603200091951320484939821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-16892817842045373585638246288280000000000000)
      constant := (345093350597484158246711186156674860442824807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329251445575794232687/100000000000000000000)
  centralHi := (20578215348487139543/6250000000000000000)
  directionLo := (33063196083632142027/10000000000000000000)
  directionHi := (330631960836321420271/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree121.table
  base := (4946428110374875323230821499533886721/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-1109630721087373111569118773996000000000000)
      constant := (22351005789008709449268828167562211730494760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree121.table
  base := (989285533145898444276299660784740832763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-51111860884771319681954549774100000000000000)
      constant := (1053742218875570048982457807445607110906016563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33063196083632142027/10000000000000000000)
  centralHi := (330631960836321420271/100000000000000000000)
  directionLo := (332006735834066130611/100000000000000000000)
  directionHi := (83001683958516532653/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree122.table
  base := (631027573857093022250374308595861041363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5595227812929078175172015279600000000000000)
      constant := (113734789109321587268095707854552407681907814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree122.table
  base := (631027535208552504039338925168198710297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-51545268243406518606994360683360000000000000)
      constant := (1072366367917321923152391034353324969690964994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332006735834066130611/100000000000000000000)
  centralHi := (83001683958516532653/25000000000000000000)
  directionLo := (6667516831682150651/2000000000000000000)
  directionHi := (333375841584107532551/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree123.table
  base := (307788782877393629128063678895081162703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-1128460404084258158499687337844000000000000)
      constant := (23146360069245252141491412359444278456021167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree123.table
  base := (1538943847204848778831266168267777309233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-17326225200680572510678057197540000000000000)
      constant := (363717499589134499224466655439462162927105011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6667516831682150651/2000000000000000000)
  centralHi := (333375841584107532551/100000000000000000000)
  directionLo := (334739347649230730503/100000000000000000000)
  directionHi := (41842418456153841313/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree124.table
  base := (909975932639445938195280441459621070517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5689376227913503409824858098840000000000000)
      constant := (117746062639338197441334326281403660978758826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree124.table
  base := (1819951806891903588829106645348543719229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-52412082960676916457073982501880000000000000)
      constant := (1110100611278553367283284007662823562213714629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334739347649230730503/100000000000000000000)
  centralHi := (41842418456153841313/12500000000000000000)
  directionLo := (336097322181169930291/100000000000000000000)
  directionHi := (84024330545292482573/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree125.table
  base := (2105078944732132220432810764483345298681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5736450435405716027151279508460000000000000)
      constant := (119777575972572286040011407030185686791318809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree125.table
  base := (2105078893992107244437070086555256567769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-52845490319312115382113793411140000000000000)
      constant := (1129210705306452024116398187350380222332767169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336097322181169930291/100000000000000000000)
  centralHi := (84024330545292482573/25000000000000000000)
  directionLo := (16872491598017891047/5000000000000000000)
  directionHi := (337449831960357820941/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree126.table
  base := (478865019641115130291760171462998615197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-1156704928579585728895540183616000000000000)
      constant := (24365268066033228938877042965602406599791933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree126.table
  base := (2394325054113762532672097079927054695589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-17759632559315771435717868106800000000000000)
      constant := (382827593569875554573924522616848756421075663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16872491598017891047/5000000000000000000)
  centralHi := (337449831960357820941/100000000000000000000)
  directionLo := (84699235608561692807/25000000000000000000)
  directionHi := (338796942434246771229/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree127.table
  base := (1343845136118732820829450186880956580657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5830598850390141261804122327700000000000000)
      constant := (123892355696669325767918766377251192903619746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree127.table
  base := (1343845116962576964217000911613202774947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-53712305036582513232193415229660000000000000)
      constant := (1167916837349361494018624565891701880835274294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84699235608561692807/25000000000000000000)
  centralHi := (338796942434246771229/100000000000000000000)
  directionLo := (170069358877132031103/50000000000000000000)
  directionHi := (340138717754264062207/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree128.table
  base := (597034882882066120226874568946673892391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (952)
      previous := (493)
      next := (0)
      square := (13797612540820939561192482130000000000000)
      linear := (-1175534611576470775826108747464000000000000)
      constant := (25195124411386635994226265367667188754900999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree128.table
  base := (2985174381121977905219881047733871350031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (42330)
      previous := (22695)
      next := (0)
      square := (620892564336942280253661695850000000000000)
      linear := (-54145712395217712157233226138920000000000000)
      constant := (1187512875089613021534517130071907799381430631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell012.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170069358877132031103/50000000000000000000)
  centralHi := (340138717754264062207/100000000000000000000)
  directionLo := (341475220811460198417/100000000000000000000)
  directionHi := (170737610405730099209/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree129.table
  base := (1643388736658984887707890686338590403511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4760)
      previous := (2465)
      next := (0)
      square := (68988062704104697805962410650000000000000)
      linear := (-5924747265374566496456965146940000000000000)
      constant := (128076139396101315285981228947873705253229358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree129.table
  base := (3286777444396509498680529777427122983097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (14110)
      previous := (7565)
      next := (0)
      square := (206964188112314093417887231950000000000000)
      linear := (-18193039917950970360757679016060000000000000)
      constant := (402423631265643284545726326082843315626345099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell012.Kernel129
