import ForestUnimodality.TiltedSourceData.Case28.Batch000

import ForestUnimodality.TiltedSourceData.Case28.Batch001

import ForestUnimodality.TiltedSourceData.Case28.Batch002

import ForestUnimodality.TiltedSourceData.Case28.Batch003

import ForestUnimodality.TiltedSourceData.Case28.Batch004

import ForestUnimodality.TiltedSourceData.Case28.Batch005

import ForestUnimodality.TiltedSourceData.Case28.Batch006

import ForestUnimodality.TiltedSourceData.Case28.Batch007

import ForestUnimodality.TiltedSourceData.Case28.Batch008

import ForestUnimodality.TiltedSourceData.Case28.Batch009

import ForestUnimodality.TiltedSourceData.Case28.Batch010

import ForestUnimodality.TiltedSourceData.Case28.Batch011

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.TiltedSourceData.Case28


def cells0 : List TiltedSource.Cell := Batch000.cells ++ Batch001.cells ++ Batch002.cells

theorem cells0_checked : cells0.all (fun c=>c.check parameters 0 domain0 domain0.b)=true := by

  simp only [cells0,List.all_append,Batch000.cells_checked, Batch001.cells_checked, Batch002.cells_checked,Bool.and_self]

theorem coverage0_checked : SourceIntervalCoverage.check TiltedSource.Cell.left TiltedSource.Cell.right

    0 (SelectionSource.probabilityCap domain0) cells0=true := by decide +kernel

def cells1 : List TiltedSource.Cell := Batch003.cells ++ Batch004.cells ++ Batch005.cells ++ Batch006.cells

theorem cells1_checked : cells1.all (fun c=>c.check parameters 1 domain0 domain1.b)=true := by

  simp only [cells1,List.all_append,Batch003.cells_checked, Batch004.cells_checked, Batch005.cells_checked, Batch006.cells_checked,Bool.and_self]

theorem coverage1_checked : SourceIntervalCoverage.check TiltedSource.Cell.left TiltedSource.Cell.right

    0 (SelectionSource.probabilityCap domain0) cells1=true := by decide +kernel

def cells2 : List TiltedSource.Cell := Batch007.cells ++ Batch008.cells ++ Batch009.cells ++ Batch010.cells ++ Batch011.cells

theorem cells2_checked : cells2.all (fun c=>c.check parameters 2 domain1 domain0.b)=true := by

  simp only [cells2,List.all_append,Batch007.cells_checked, Batch008.cells_checked, Batch009.cells_checked, Batch010.cells_checked, Batch011.cells_checked,Bool.and_self]

theorem coverage2_checked : SourceIntervalCoverage.check TiltedSource.Cell.left TiltedSource.Cell.right

    0 (SelectionSource.probabilityCap domain1) cells2=true := by decide +kernel

def cells (s : Fin 3) : List TiltedSource.Cell :=
  if s=0 then cells0 else if s=1 then cells1 else cells2

theorem cells_checked (s : Fin 3) :
    (cells s).all (fun c=>c.check parameters s (TiltedSource.sourceDomain domain0 domain1 s)
      (TiltedSource.parentCap domain0 domain1 s))=true := by
  fin_cases s
  · simpa [cells,TiltedSource.sourceDomain,TiltedSource.parentCap] using cells0_checked
  · simpa [cells,TiltedSource.sourceDomain,TiltedSource.parentCap] using cells1_checked
  · simpa [cells,TiltedSource.sourceDomain,TiltedSource.parentCap] using cells2_checked

theorem coverage_checked (s : Fin 3) :
    SourceIntervalCoverage.check TiltedSource.Cell.left TiltedSource.Cell.right 0
      (SelectionSource.probabilityCap (TiltedSource.sourceDomain domain0 domain1 s)) (cells s)=true := by
  fin_cases s
  · simpa [cells,TiltedSource.sourceDomain] using coverage0_checked
  · simpa [cells,TiltedSource.sourceDomain] using coverage1_checked
  · simpa [cells,TiltedSource.sourceDomain] using coverage2_checked

theorem source_valid : TiltedSourceRowValid parameters.toReal (tiltedMarkCap domain0.b domain1.b) :=
  TiltedSource.sourceRowValid_of_checked parameters domain0 domain1 cells parameters_checked
    domain0_checked domain1_checked leaf_checked cells_checked coverage_checked

#print axioms source_valid


end ForestUnimodality.TiltedSourceData.Case28
