import { integer, sqliteTable, text } from "drizzle-orm/sqlite-core";

export const siteCounters = sqliteTable("site_counters", {
  name: text("name").primaryKey(),
  value: integer("value").notNull().default(0),
});
