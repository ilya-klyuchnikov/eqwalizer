%%% Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
%%%
%%% This source code is licensed under the Apache 2.0 license found in
%%% the LICENSE file in the root directory of this source tree.

-module(otp26).
-feature(maybe_expr, enable).
-compile([export_all, nowarn_export_all]).

% simple maybe
maybe1(A) ->
  maybe
    A
  end.

% maybe else
maybe2(A, B, C) ->
  maybe
    A ?= B
  else
    _ -> C
  end.

comp1(M) ->
  #{Key => Value || Key := Value <- M}.

comp2(M) ->
  [{Key, Value} || Key := Value <- M].

comp3(M) ->
  << <<Key/binary, Value/binary>> || Key := Value <- M >>.

comp4(List) ->
  #{Key => Value || {Key, Value} <- List}.

comp5(Bin) ->
  #{X => true || <<X>> <= Bin}.
