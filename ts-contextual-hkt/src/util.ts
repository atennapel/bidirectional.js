export const impossible = (msg?: string): any => { throw new Error(msg || 'impossible') };

export const time = <T>(fn: () => T) => {
  const t = Date.now();
  const val = fn();
  const time = Date.now() - t;
  return { time, val };
};
