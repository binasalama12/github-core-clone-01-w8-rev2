// Entry lifecycle for the unit-of-work forge: build the app, listen on an
// ephemeral port, register with the make.fun environment, wait until the
// environment signals completion, then shut down cleanly.
import { createApp } from './app.ts';

const envUrl = process.env.MAKEFUN_ENV_URL;
if (!envUrl) {
  console.error('MAKEFUN_ENV_URL is not set');
  process.exit(1);
}

const app = createApp();
await new Promise<void>((resolve) => {
  app.listen(0, () => resolve());
});
const address = app.address();
if (address === null || typeof address === 'string') {
  console.error('server did not bind a TCP port');
  process.exit(1);
}
const port = address.port;

async function registerWithRetry(): Promise<void> {
  for (;;) {
    const response = await fetch(`${envUrl}/register`, {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ port }),
    });
    if (response.status === 200 || response.status === 409) return;
    if (response.status === 400 || response.status === 405) {
      throw new Error(`registration rejected with status ${response.status}`);
    }
    await new Promise((resolve) => setTimeout(resolve, 500));
  }
}

await registerWithRetry();

for (;;) {
  const response = await fetch(`${envUrl}/done`);
  if (response.ok) {
    const body = (await response.json()) as { done?: boolean };
    if (body.done === true) break;
  }
  await new Promise((resolve) => setTimeout(resolve, 250));
}

await new Promise<void>((resolve) => {
  app.close(() => resolve());
});
process.exit(0);
