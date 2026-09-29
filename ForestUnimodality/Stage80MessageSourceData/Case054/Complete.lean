import ForestUnimodality.Stage80MessageSourceData.Case054.Batch000

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch001

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch002

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch003

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch004

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch005

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch006

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch007

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch008

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch009

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch010

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch011

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch012

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch013

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch014

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch015

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch016

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch017

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch018

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch019

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch020

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch021

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch022

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch023

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch024

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch025

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch026

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch027

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch028

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch029

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch030

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch031

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch032

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch033

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch034

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch035

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch036

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch037

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch038

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch039

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch040

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch041

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch042

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch043

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch044

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch045

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch046

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch047

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch048

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch049

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch050

import ForestUnimodality.Stage80MessageSourceData.Case054.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.Stage80MessageSourceData.Case054
open MessagePriceSpline MessageCells


def cells : List Cell := Batch000.cells ++ Batch001.cells ++ Batch002.cells ++ Batch003.cells ++ Batch004.cells ++ Batch005.cells ++ Batch006.cells ++ Batch007.cells ++ Batch008.cells ++ Batch009.cells ++ Batch010.cells ++ Batch011.cells ++ Batch012.cells ++ Batch013.cells ++ Batch014.cells ++ Batch015.cells ++ Batch016.cells ++ Batch017.cells ++ Batch018.cells ++ Batch019.cells ++ Batch020.cells ++ Batch021.cells ++ Batch022.cells ++ Batch023.cells ++ Batch024.cells ++ Batch025.cells ++ Batch026.cells ++ Batch027.cells ++ Batch028.cells ++ Batch029.cells ++ Batch030.cells ++ Batch031.cells ++ Batch032.cells ++ Batch033.cells ++ Batch034.cells ++ Batch035.cells ++ Batch036.cells ++ Batch037.cells ++ Batch038.cells ++ Batch039.cells ++ Batch040.cells ++ Batch041.cells ++ Batch042.cells ++ Batch043.cells ++ Batch044.cells ++ Batch045.cells ++ Batch046.cells ++ Batch047.cells ++ Batch048.cells ++ Batch049.cells ++ Batch050.cells ++ Batch051.cells

theorem cells_checked : cells.all (fun c=>c.check parameters domain)=true := by

  simp only [cells,List.all_append,Batch000.cells_checked, Batch001.cells_checked, Batch002.cells_checked, Batch003.cells_checked, Batch004.cells_checked, Batch005.cells_checked, Batch006.cells_checked, Batch007.cells_checked, Batch008.cells_checked, Batch009.cells_checked, Batch010.cells_checked, Batch011.cells_checked, Batch012.cells_checked, Batch013.cells_checked, Batch014.cells_checked, Batch015.cells_checked, Batch016.cells_checked, Batch017.cells_checked, Batch018.cells_checked, Batch019.cells_checked, Batch020.cells_checked, Batch021.cells_checked, Batch022.cells_checked, Batch023.cells_checked, Batch024.cells_checked, Batch025.cells_checked, Batch026.cells_checked, Batch027.cells_checked, Batch028.cells_checked, Batch029.cells_checked, Batch030.cells_checked, Batch031.cells_checked, Batch032.cells_checked, Batch033.cells_checked, Batch034.cells_checked, Batch035.cells_checked, Batch036.cells_checked, Batch037.cells_checked, Batch038.cells_checked, Batch039.cells_checked, Batch040.cells_checked, Batch041.cells_checked, Batch042.cells_checked, Batch043.cells_checked, Batch044.cells_checked, Batch045.cells_checked, Batch046.cells_checked, Batch047.cells_checked, Batch048.cells_checked, Batch049.cells_checked, Batch050.cells_checked, Batch051.cells_checked,Bool.and_self]

theorem coverage_checked : SourceIntervalCoverage.check Cell.left Cell.right 0 (SelectionSource.probabilityCap domain) cells=true := by decide +kernel

theorem source_valid : MessageSourceRowValid parameters.toReal domain.lower domain.b :=

  sourceRowValid_of_checked parameters domain monotonic cap cells parameters_checked domain_checked monotonic_checked cap_checked cells_checked coverage_checked

#print axioms source_valid

end ForestUnimodality.Stage80MessageSourceData.Case054
