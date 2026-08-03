const CREATE_COUNTER_TABLE = `
  CREATE TABLE IF NOT EXISTS site_counters (
    name TEXT PRIMARY KEY NOT NULL,
    value INTEGER NOT NULL DEFAULT 0
  )
`;

const INCREMENT_PAGE_VIEWS = `
  INSERT INTO site_counters (name, value)
  VALUES ('page_views', 1)
  ON CONFLICT(name) DO UPDATE SET value = value + 1
`;

export async function incrementPageViews(db: D1Database): Promise<void> {
  await db.batch([
    db.prepare(CREATE_COUNTER_TABLE),
    db.prepare(INCREMENT_PAGE_VIEWS),
  ]);
}

export async function readPageViews(db: D1Database): Promise<number> {
  await db.prepare(CREATE_COUNTER_TABLE).run();
  const row = await db
    .prepare("SELECT value FROM site_counters WHERE name = 'page_views'")
    .first<{ value: number }>();
  return row?.value ?? 0;
}
