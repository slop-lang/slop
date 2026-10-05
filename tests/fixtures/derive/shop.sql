-- Shop schema: exercises the column forms slop derive must keep.

CREATE TYPE order_state AS ENUM ('new', 'paid', 'shipped');

CREATE TABLE IF NOT EXISTS users (
    id INTEGER PRIMARY KEY,
    email VARCHAR(255) UNIQUE NOT NULL,
    display_name VARCHAR(100),
    age INT(11) CHECK (age >= 0),
    checksum CHAR(64) NOT NULL,
    index_id BIGINT,
    created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, -- creation time
    is_admin BOOLEAN DEFAULT FALSE
);

CREATE TABLE "public"."order items" (
    "order id" BIGSERIAL,
    `sku` VARCHAR(32) NOT NULL,
    [unit price] DECIMAL(10, 2) NOT NULL,
    weight FLOAT(53),
    ratio FLOAT,
    quantity SMALLINT UNSIGNED NOT NULL,
    state order_state NOT NULL,
    note TEXT,
    payload JSONB,
    tags TEXT[],
    geom GEOMETRY,
    key VARCHAR(10),
    CONSTRAINT pk_order_items PRIMARY KEY ("order id", sku),
    FOREIGN KEY (sku) REFERENCES products (sku),
    UNIQUE (sku, weight),
    CHECK (quantity > 0)
);

CREATE TABLE products (
    sku VARCHAR(32) NOT NULL,
    id SERIAL,
    price NUMERIC(12,4),
    PRIMARY KEY (sku),
    KEY idx_price (price)
);
