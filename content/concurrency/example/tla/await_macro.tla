macro make_calls(n)
begin
  await made_calls <= max_calls - n;
  made_calls := made_calls + n;
  assert made_calls <= max_calls;
end macro;
